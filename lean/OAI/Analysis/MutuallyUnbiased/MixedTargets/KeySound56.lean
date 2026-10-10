import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical321
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical322

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1792) =
      Integer.Sparse.eval keyMomentRow1792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3583) := by
    have ha : gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge = raw41205 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41205Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41205 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1792).leftCharge (GramAssembly.key 1792).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1792, Integer.Sparse.eval]

theorem keyMoment1793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1793) =
      Integer.Sparse.eval keyMomentRow1793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3397) := by
    have ha : gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge = raw41206 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41206Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41206 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1793).leftCharge (GramAssembly.key 1793).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1793, Integer.Sparse.eval]

theorem keyMoment1794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1794) =
      Integer.Sparse.eval keyMomentRow1794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3548) := by
    have ha : gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge = raw41207 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41207Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41207 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1794).leftCharge (GramAssembly.key 1794).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1794, Integer.Sparse.eval]

theorem keyMoment1795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1795) =
      Integer.Sparse.eval keyMomentRow1795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge = raw41208 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41208Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41208 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1795).leftCharge (GramAssembly.key 1795).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1795, Integer.Sparse.eval]

theorem keyMoment1796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1796) =
      Integer.Sparse.eval keyMomentRow1796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3394) := by
    have ha : gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge = raw41209 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41209Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41209 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1796).leftCharge (GramAssembly.key 1796).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1796, Integer.Sparse.eval]

theorem keyMoment1797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1797) =
      Integer.Sparse.eval keyMomentRow1797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge = raw41210 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41210Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41210 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1797).leftCharge (GramAssembly.key 1797).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1797, Integer.Sparse.eval]

theorem keyMoment1798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1798) =
      Integer.Sparse.eval keyMomentRow1798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3496) := by
    have ha : gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge = raw41211 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41211Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41211 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1798).leftCharge (GramAssembly.key 1798).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1798, Integer.Sparse.eval]

theorem keyMoment1799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1799) =
      Integer.Sparse.eval keyMomentRow1799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge = raw41212 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41212Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41212 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1799).leftCharge (GramAssembly.key 1799).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1799, Integer.Sparse.eval]

theorem keyMoment1800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1800) =
      Integer.Sparse.eval keyMomentRow1800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2522) := by
    have ha : gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge = raw41213 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41213Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41213 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1800).leftCharge (GramAssembly.key 1800).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1800, Integer.Sparse.eval]

theorem keyMoment1801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1801) =
      Integer.Sparse.eval keyMomentRow1801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge = raw41214 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41214Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41214 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1801).leftCharge (GramAssembly.key 1801).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1801, Integer.Sparse.eval]

theorem keyMoment1802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1802) =
      Integer.Sparse.eval keyMomentRow1802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1094) := by
    have ha : gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge = raw41215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41215 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1802).leftCharge (GramAssembly.key 1802).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1802, Integer.Sparse.eval]

theorem keyMoment1803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1803) =
      Integer.Sparse.eval keyMomentRow1803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2291) := by
    have ha : gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge = raw41216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41216 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1803).leftCharge (GramAssembly.key 1803).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1803, Integer.Sparse.eval]

theorem keyMoment1804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1804) =
      Integer.Sparse.eval keyMomentRow1804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge = raw41217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41217 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1804).leftCharge (GramAssembly.key 1804).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1804, Integer.Sparse.eval]

theorem keyMoment1805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1805) =
      Integer.Sparse.eval keyMomentRow1805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge = raw41218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41218 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1805).leftCharge (GramAssembly.key 1805).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1805, Integer.Sparse.eval]

theorem keyMoment1806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1806) =
      Integer.Sparse.eval keyMomentRow1806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3816) := by
    have ha : gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge = raw41219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41219 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1806).leftCharge (GramAssembly.key 1806).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1806, Integer.Sparse.eval]

theorem keyMoment1807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1807) =
      Integer.Sparse.eval keyMomentRow1807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge = raw41220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41220 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1807).leftCharge (GramAssembly.key 1807).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1807, Integer.Sparse.eval]

theorem keyMoment1808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1808) =
      Integer.Sparse.eval keyMomentRow1808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge = raw41221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41221 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1808).leftCharge (GramAssembly.key 1808).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1808, Integer.Sparse.eval]

theorem keyMoment1809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1809) =
      Integer.Sparse.eval keyMomentRow1809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge = raw41222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41222 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1809).leftCharge (GramAssembly.key 1809).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1809, Integer.Sparse.eval]

theorem keyMoment1810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1810) =
      Integer.Sparse.eval keyMomentRow1810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge = raw41223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41223 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1810).leftCharge (GramAssembly.key 1810).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1810, Integer.Sparse.eval]

theorem keyMoment1811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1811) =
      Integer.Sparse.eval keyMomentRow1811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge = raw41224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41224 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1811).leftCharge (GramAssembly.key 1811).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1811, Integer.Sparse.eval]

theorem keyMoment1812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1812) =
      Integer.Sparse.eval keyMomentRow1812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge = raw41225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41225 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1812).leftCharge (GramAssembly.key 1812).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1812, Integer.Sparse.eval]

theorem keyMoment1813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1813) =
      Integer.Sparse.eval keyMomentRow1813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge = raw41226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41226 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1813).leftCharge (GramAssembly.key 1813).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1813, Integer.Sparse.eval]

theorem keyMoment1814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1814) =
      Integer.Sparse.eval keyMomentRow1814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge = raw41227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41227 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1814).leftCharge (GramAssembly.key 1814).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1814, Integer.Sparse.eval]

theorem keyMoment1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1815) =
      Integer.Sparse.eval keyMomentRow1815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3983) := by
    have ha : gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge = raw41228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41228 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1815).leftCharge (GramAssembly.key 1815).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1815, Integer.Sparse.eval]

theorem keyMoment1816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1816) =
      Integer.Sparse.eval keyMomentRow1816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge = raw41229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41229 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1816).leftCharge (GramAssembly.key 1816).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1816, Integer.Sparse.eval]

theorem keyMoment1817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1817) =
      Integer.Sparse.eval keyMomentRow1817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge = raw41230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41230 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1817).leftCharge (GramAssembly.key 1817).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1817, Integer.Sparse.eval]

theorem keyMoment1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1818) =
      Integer.Sparse.eval keyMomentRow1818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge = raw41231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41231 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1818).leftCharge (GramAssembly.key 1818).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1818, Integer.Sparse.eval]

theorem keyMoment1819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1819) =
      Integer.Sparse.eval keyMomentRow1819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge = raw41232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1819).leftCharge (GramAssembly.key 1819).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1819, Integer.Sparse.eval]

theorem keyMoment1820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1820) =
      Integer.Sparse.eval keyMomentRow1820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3908) := by
    have ha : gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge = raw41233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41233 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1820).leftCharge (GramAssembly.key 1820).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1820, Integer.Sparse.eval]

theorem keyMoment1821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1821) =
      Integer.Sparse.eval keyMomentRow1821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge = raw41234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41234 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1821).leftCharge (GramAssembly.key 1821).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1821, Integer.Sparse.eval]

theorem keyMoment1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1822) =
      Integer.Sparse.eval keyMomentRow1822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge = raw41235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41235 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1822).leftCharge (GramAssembly.key 1822).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1822, Integer.Sparse.eval]

theorem keyMoment1823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1823) =
      Integer.Sparse.eval keyMomentRow1823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3627) := by
    have ha : gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge = raw41236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41236 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1823).leftCharge (GramAssembly.key 1823).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1823, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
