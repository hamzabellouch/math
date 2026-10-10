import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical324

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2112) =
      Integer.Sparse.eval keyMomentRow2112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 0) := by
    have ha : gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge = raw41536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41536 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge = raw41537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41537 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2112).leftCharge (GramAssembly.key 2112).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2112, Integer.Sparse.eval]
  ring

theorem keyMoment2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2113) =
      Integer.Sparse.eval keyMomentRow2113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge = raw41538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41538 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge = raw41539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41539 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2113).leftCharge (GramAssembly.key 2113).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2113, Integer.Sparse.eval]
  ring

theorem keyMoment2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2114) =
      Integer.Sparse.eval keyMomentRow2114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3227) := by
    have ha : gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge = raw41540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41540 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4888) := by
    have ha : gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge = raw41541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41541 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2114).leftCharge (GramAssembly.key 2114).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2114, Integer.Sparse.eval]
  ring

theorem keyMoment2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2115) =
      Integer.Sparse.eval keyMomentRow2115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3228) := by
    have ha : gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge = raw41542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41542 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4893) := by
    have ha : gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge = raw41543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41543 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2115).leftCharge (GramAssembly.key 2115).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2115, Integer.Sparse.eval]
  ring

theorem keyMoment2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2116) =
      Integer.Sparse.eval keyMomentRow2116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3223) := by
    have ha : gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge = raw41544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41544 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4889) := by
    have ha : gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge = raw41545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41545 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2116).leftCharge (GramAssembly.key 2116).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2116, Integer.Sparse.eval]
  ring

theorem keyMoment2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2117) =
      Integer.Sparse.eval keyMomentRow2117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3226) := by
    have ha : gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge = raw41546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41546 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4887) := by
    have ha : gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge = raw41547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41547 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2117).leftCharge (GramAssembly.key 2117).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2117, Integer.Sparse.eval]
  ring

theorem keyMoment2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2118) =
      Integer.Sparse.eval keyMomentRow2118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge = raw41548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41548 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge = raw41549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41549 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2118).leftCharge (GramAssembly.key 2118).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2118, Integer.Sparse.eval]
  ring

theorem keyMoment2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2119) =
      Integer.Sparse.eval keyMomentRow2119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3113) := by
    have ha : gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge = raw41550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41550 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5272) := by
    have ha : gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge = raw41551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41551 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2119).leftCharge (GramAssembly.key 2119).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2119, Integer.Sparse.eval]
  ring

theorem keyMoment2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2120) =
      Integer.Sparse.eval keyMomentRow2120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge = raw41552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41552 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge = raw41553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41553 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2120).leftCharge (GramAssembly.key 2120).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2120, Integer.Sparse.eval]
  ring

theorem keyMoment2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2121) =
      Integer.Sparse.eval keyMomentRow2121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge = raw41554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41554 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge = raw41555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41555 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2121).leftCharge (GramAssembly.key 2121).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2121, Integer.Sparse.eval]
  ring

theorem keyMoment2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2122) =
      Integer.Sparse.eval keyMomentRow2122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge = raw41556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41556 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge = raw41557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41557 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2122).leftCharge (GramAssembly.key 2122).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2122, Integer.Sparse.eval]
  ring

theorem keyMoment2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2123) =
      Integer.Sparse.eval keyMomentRow2123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge = raw41558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41558 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge = raw41559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41559 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2123).leftCharge (GramAssembly.key 2123).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2123, Integer.Sparse.eval]
  ring

theorem keyMoment2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2124) =
      Integer.Sparse.eval keyMomentRow2124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3088) := by
    have ha : gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge = raw41560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41560 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5259) := by
    have ha : gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge = raw41561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41561 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2124).leftCharge (GramAssembly.key 2124).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2124, Integer.Sparse.eval]
  ring

theorem keyMoment2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2125) =
      Integer.Sparse.eval keyMomentRow2125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge = raw41562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41562 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge = raw41563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41563 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2125).leftCharge (GramAssembly.key 2125).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2125, Integer.Sparse.eval]
  ring

theorem keyMoment2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2126) =
      Integer.Sparse.eval keyMomentRow2126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge = raw41564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41564 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge = raw41565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41565 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2126).leftCharge (GramAssembly.key 2126).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2126, Integer.Sparse.eval]
  ring

theorem keyMoment2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2127) =
      Integer.Sparse.eval keyMomentRow2127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge = raw41566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41566 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge = raw41567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41567 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2127).leftCharge (GramAssembly.key 2127).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2127, Integer.Sparse.eval]
  ring

theorem keyMoment2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2128) =
      Integer.Sparse.eval keyMomentRow2128 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3109) := by
    have ha : gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge = raw41568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41568 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5271) := by
    have ha : gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge = raw41569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41569 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2128).leftCharge (GramAssembly.key 2128).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2128, Integer.Sparse.eval]
  ring

theorem keyMoment2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2129) =
      Integer.Sparse.eval keyMomentRow2129 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3111) := by
    have ha : gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge = raw41570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41570 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5273) := by
    have ha : gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge = raw41571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41571 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2129).leftCharge (GramAssembly.key 2129).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2129, Integer.Sparse.eval]
  ring

theorem keyMoment2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2130) =
      Integer.Sparse.eval keyMomentRow2130 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge = raw41572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41572 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge = raw41573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41573 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2130).leftCharge (GramAssembly.key 2130).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2130, Integer.Sparse.eval]
  ring

theorem keyMoment2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2131) =
      Integer.Sparse.eval keyMomentRow2131 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3085) := by
    have ha : gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge = raw41574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41574 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5256) := by
    have ha : gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge = raw41575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41575 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2131).leftCharge (GramAssembly.key 2131).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2131, Integer.Sparse.eval]
  ring

theorem keyMoment2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2132) =
      Integer.Sparse.eval keyMomentRow2132 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3087) := by
    have ha : gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge = raw41576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41576 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5257) := by
    have ha : gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge = raw41577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41577 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2132).leftCharge (GramAssembly.key 2132).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2132, Integer.Sparse.eval]
  ring

theorem keyMoment2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2133) =
      Integer.Sparse.eval keyMomentRow2133 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge = raw41578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41578 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge = raw41579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41579 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2133).leftCharge (GramAssembly.key 2133).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2133, Integer.Sparse.eval]
  ring

theorem keyMoment2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2134) =
      Integer.Sparse.eval keyMomentRow2134 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3125) := by
    have ha : gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge = raw41580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41580 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5305) := by
    have ha : gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge = raw41581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41581 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2134).leftCharge (GramAssembly.key 2134).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2134, Integer.Sparse.eval]
  ring

theorem keyMoment2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2135) =
      Integer.Sparse.eval keyMomentRow2135 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge = raw41582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41582 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5311) := by
    have ha : gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge = raw41583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41583 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2135).leftCharge (GramAssembly.key 2135).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2135, Integer.Sparse.eval]
  ring

theorem keyMoment2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2136) =
      Integer.Sparse.eval keyMomentRow2136 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3103) := by
    have ha : gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge = raw41584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41584 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5291) := by
    have ha : gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge = raw41585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41585 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2136).leftCharge (GramAssembly.key 2136).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2136, Integer.Sparse.eval]
  ring

theorem keyMoment2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2137) =
      Integer.Sparse.eval keyMomentRow2137 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge = raw41586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41586 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge = raw41587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41587 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2137).leftCharge (GramAssembly.key 2137).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2137, Integer.Sparse.eval]
  ring

theorem keyMoment2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2138) =
      Integer.Sparse.eval keyMomentRow2138 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge = raw41588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41588 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge = raw41589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41589 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2138).leftCharge (GramAssembly.key 2138).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2138, Integer.Sparse.eval]
  ring

theorem keyMoment2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2139) =
      Integer.Sparse.eval keyMomentRow2139 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge = raw41590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41590 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge = raw41591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41591 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2139).leftCharge (GramAssembly.key 2139).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2139, Integer.Sparse.eval]
  ring

theorem keyMoment2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2140) =
      Integer.Sparse.eval keyMomentRow2140 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3119) := by
    have ha : gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge = raw41592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41592 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5304) := by
    have ha : gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge = raw41593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41593 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2140).leftCharge (GramAssembly.key 2140).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2140, Integer.Sparse.eval]
  ring

theorem keyMoment2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2141) =
      Integer.Sparse.eval keyMomentRow2141 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge = raw41594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41594 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge = raw41595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41595 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2141).leftCharge (GramAssembly.key 2141).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2141, Integer.Sparse.eval]
  ring

theorem keyMoment2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2142) =
      Integer.Sparse.eval keyMomentRow2142 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge = raw41596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41596 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5289) := by
    have ha : gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge = raw41597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41597 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2142).leftCharge (GramAssembly.key 2142).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2142, Integer.Sparse.eval]
  ring

theorem keyMoment2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2143) =
      Integer.Sparse.eval keyMomentRow2143 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3099) := by
    have ha : gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge = raw41598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41598 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5290) := by
    have ha : gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge = raw41599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41599 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2143).leftCharge (GramAssembly.key 2143).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2143, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
