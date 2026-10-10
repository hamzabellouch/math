import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical330

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2496) =
      Integer.Sparse.eval keyMomentRow2496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3565) := by
    have ha : gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge = raw42304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42304 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5164) := by
    have ha : gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge = raw42305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42305 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2496, Integer.Sparse.eval]; ring

theorem keyMoment2497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2497) =
      Integer.Sparse.eval keyMomentRow2497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge = raw42306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42306 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge = raw42307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42307 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2497, Integer.Sparse.eval]; ring

theorem keyMoment2498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2498) =
      Integer.Sparse.eval keyMomentRow2498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3960) := by
    have ha : gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge = raw42308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42308 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5463) := by
    have ha : gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge = raw42309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42309 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2498, Integer.Sparse.eval]; ring

theorem keyMoment2499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2499) =
      Integer.Sparse.eval keyMomentRow2499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3562) := by
    have ha : gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge = raw42310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42310 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5145) := by
    have ha : gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge = raw42311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42311 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2499, Integer.Sparse.eval]; ring

theorem keyMoment2500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2500) =
      Integer.Sparse.eval keyMomentRow2500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge = raw42312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42312 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge = raw42313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42313 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2500, Integer.Sparse.eval]; ring

theorem keyMoment2501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2501) =
      Integer.Sparse.eval keyMomentRow2501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge = raw42314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42314 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge = raw42315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42315 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2501, Integer.Sparse.eval]; ring

theorem keyMoment2502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2502) =
      Integer.Sparse.eval keyMomentRow2502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge = raw42316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42316 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge = raw42317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42317 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2502, Integer.Sparse.eval]; ring

theorem keyMoment2503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2503) =
      Integer.Sparse.eval keyMomentRow2503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge = raw42318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42318 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge = raw42319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42319 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2503, Integer.Sparse.eval]; ring

theorem keyMoment2504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2504) =
      Integer.Sparse.eval keyMomentRow2504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3529) := by
    have ha : gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge = raw42320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42320 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5185) := by
    have ha : gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge = raw42321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42321 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2504, Integer.Sparse.eval]; ring

theorem keyMoment2505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2505) =
      Integer.Sparse.eval keyMomentRow2505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge = raw42322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42322 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge = raw42323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42323 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2505, Integer.Sparse.eval]; ring

theorem keyMoment2506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2506) =
      Integer.Sparse.eval keyMomentRow2506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge = raw42324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42324 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge = raw42325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42325 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2506, Integer.Sparse.eval]; ring

theorem keyMoment2507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2507) =
      Integer.Sparse.eval keyMomentRow2507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge = raw42326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42326 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge = raw42327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42327 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2507, Integer.Sparse.eval]; ring

theorem keyMoment2508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2508) =
      Integer.Sparse.eval keyMomentRow2508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge = raw42328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42328 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge = raw42329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42329 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2508, Integer.Sparse.eval]; ring

theorem keyMoment2509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2509) =
      Integer.Sparse.eval keyMomentRow2509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge = raw42330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42330 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge = raw42331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42331 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2509, Integer.Sparse.eval]; ring

theorem keyMoment2510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2510) =
      Integer.Sparse.eval keyMomentRow2510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge = raw42332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42332 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge = raw42333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42333 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2510, Integer.Sparse.eval]; ring

theorem keyMoment2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2511) =
      Integer.Sparse.eval keyMomentRow2511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge = raw42334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42334 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge = raw42335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42335 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2511, Integer.Sparse.eval]; ring

theorem keyMoment2512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2512) =
      Integer.Sparse.eval keyMomentRow2512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2680) := by
    have ha : gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge = raw42336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42336 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5235) := by
    have ha : gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge = raw42337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42337 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2512, Integer.Sparse.eval]; ring

theorem keyMoment2513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2513) =
      Integer.Sparse.eval keyMomentRow2513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge = raw42338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42338 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge = raw42339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42339 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2513, Integer.Sparse.eval]; ring

theorem keyMoment2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2514) =
      Integer.Sparse.eval keyMomentRow2514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge = raw42340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42340 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge = raw42341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42341 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2514, Integer.Sparse.eval]; ring

theorem keyMoment2515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2515) =
      Integer.Sparse.eval keyMomentRow2515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2678) := by
    have ha : gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge = raw42342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42342 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5233) := by
    have ha : gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge = raw42343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42343 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2515, Integer.Sparse.eval]; ring

theorem keyMoment2516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2516) =
      Integer.Sparse.eval keyMomentRow2516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge = raw42344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42344 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge = raw42345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42345 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2516, Integer.Sparse.eval]; ring

theorem keyMoment2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2517) =
      Integer.Sparse.eval keyMomentRow2517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2664) := by
    have ha : gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge = raw42346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42346 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5222) := by
    have ha : gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge = raw42347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42347 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2517, Integer.Sparse.eval]; ring

theorem keyMoment2518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2518) =
      Integer.Sparse.eval keyMomentRow2518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge = raw42348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42348 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge = raw42349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42349 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2518, Integer.Sparse.eval]; ring

theorem keyMoment2519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2519) =
      Integer.Sparse.eval keyMomentRow2519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2775) := by
    have ha : gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge = raw42350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42350 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5301) := by
    have ha : gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge = raw42351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42351 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2519, Integer.Sparse.eval]; ring

theorem keyMoment2520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2520) =
      Integer.Sparse.eval keyMomentRow2520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge = raw42352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42352 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge = raw42353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42353 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2520, Integer.Sparse.eval]; ring

theorem keyMoment2521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2521) =
      Integer.Sparse.eval keyMomentRow2521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2698) := by
    have ha : gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge = raw42354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42354 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5244) := by
    have ha : gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge = raw42355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42355 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2521, Integer.Sparse.eval]; ring

theorem keyMoment2522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2522) =
      Integer.Sparse.eval keyMomentRow2522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge = raw42356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42356 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge = raw42357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42357 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2522, Integer.Sparse.eval]; ring

theorem keyMoment2523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2523) =
      Integer.Sparse.eval keyMomentRow2523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge = raw42358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42358 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge = raw42359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42359 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2523, Integer.Sparse.eval]; ring

theorem keyMoment2524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2524) =
      Integer.Sparse.eval keyMomentRow2524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge = raw42360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42360 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge = raw42361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42361 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2524, Integer.Sparse.eval]; ring

theorem keyMoment2525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2525) =
      Integer.Sparse.eval keyMomentRow2525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge = raw42362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42362 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge = raw42363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42363 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2525, Integer.Sparse.eval]; ring

theorem keyMoment2526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2526) =
      Integer.Sparse.eval keyMomentRow2526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge = raw42364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42364 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge = raw42365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42365 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2526, Integer.Sparse.eval]; ring

theorem keyMoment2527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2527) =
      Integer.Sparse.eval keyMomentRow2527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge = raw42366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42366 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge = raw42367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42367 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2527, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
