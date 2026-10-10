import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical321

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1760) =
      Integer.Sparse.eval keyMomentRow1760 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 611) := by
    have ha : gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge = raw41173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41173 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1760).leftCharge (GramAssembly.key 1760).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1760, Integer.Sparse.eval]

theorem keyMoment1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1761) =
      Integer.Sparse.eval keyMomentRow1761 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 603) := by
    have ha : gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge = raw41174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41174 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1761).leftCharge (GramAssembly.key 1761).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1761, Integer.Sparse.eval]

theorem keyMoment1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1762) =
      Integer.Sparse.eval keyMomentRow1762 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 615) := by
    have ha : gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge = raw41175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41175 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1762).leftCharge (GramAssembly.key 1762).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1762, Integer.Sparse.eval]

theorem keyMoment1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1763) =
      Integer.Sparse.eval keyMomentRow1763 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 605) := by
    have ha : gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge = raw41176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41176 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1763).leftCharge (GramAssembly.key 1763).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1763, Integer.Sparse.eval]

theorem keyMoment1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1764) =
      Integer.Sparse.eval keyMomentRow1764 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 614) := by
    have ha : gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge = raw41177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41177 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1764).leftCharge (GramAssembly.key 1764).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1764, Integer.Sparse.eval]

theorem keyMoment1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1765) =
      Integer.Sparse.eval keyMomentRow1765 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 622) := by
    have ha : gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge = raw41178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1765).leftCharge (GramAssembly.key 1765).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1765, Integer.Sparse.eval]

theorem keyMoment1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1766) =
      Integer.Sparse.eval keyMomentRow1766 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 619) := by
    have ha : gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge = raw41179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41179 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1766).leftCharge (GramAssembly.key 1766).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1766, Integer.Sparse.eval]

theorem keyMoment1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1767) =
      Integer.Sparse.eval keyMomentRow1767 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2738) := by
    have ha : gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge = raw41180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41180 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1767).leftCharge (GramAssembly.key 1767).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1767, Integer.Sparse.eval]

theorem keyMoment1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1768) =
      Integer.Sparse.eval keyMomentRow1768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3050) := by
    have ha : gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge = raw41181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41181 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1768).leftCharge (GramAssembly.key 1768).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1768, Integer.Sparse.eval]

theorem keyMoment1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1769) =
      Integer.Sparse.eval keyMomentRow1769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3625) := by
    have ha : gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge = raw41182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41182 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1769).leftCharge (GramAssembly.key 1769).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1769, Integer.Sparse.eval]

theorem keyMoment1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1770) =
      Integer.Sparse.eval keyMomentRow1770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge = raw41183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41183 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1770).leftCharge (GramAssembly.key 1770).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1770, Integer.Sparse.eval]

theorem keyMoment1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1771) =
      Integer.Sparse.eval keyMomentRow1771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3073) := by
    have ha : gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge = raw41184 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41184Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41184 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1771).leftCharge (GramAssembly.key 1771).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1771, Integer.Sparse.eval]

theorem keyMoment1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1772) =
      Integer.Sparse.eval keyMomentRow1772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3571) := by
    have ha : gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge = raw41185 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41185Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41185 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1772).leftCharge (GramAssembly.key 1772).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1772, Integer.Sparse.eval]

theorem keyMoment1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1773) =
      Integer.Sparse.eval keyMomentRow1773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3388) := by
    have ha : gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge = raw41186 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41186Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41186 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1773).leftCharge (GramAssembly.key 1773).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1773, Integer.Sparse.eval]

theorem keyMoment1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1774) =
      Integer.Sparse.eval keyMomentRow1774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3375) := by
    have ha : gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge = raw41187 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41187Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41187 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1774).leftCharge (GramAssembly.key 1774).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1774, Integer.Sparse.eval]

theorem keyMoment1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1775) =
      Integer.Sparse.eval keyMomentRow1775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2781) := by
    have ha : gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge = raw41188 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41188Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41188 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1775).leftCharge (GramAssembly.key 1775).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1775, Integer.Sparse.eval]

theorem keyMoment1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1776) =
      Integer.Sparse.eval keyMomentRow1776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3096) := by
    have ha : gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge = raw41189 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41189Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41189 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1776).leftCharge (GramAssembly.key 1776).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1776, Integer.Sparse.eval]

theorem keyMoment1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1777) =
      Integer.Sparse.eval keyMomentRow1777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3572) := by
    have ha : gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge = raw41190 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41190Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41190 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1777).leftCharge (GramAssembly.key 1777).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1777, Integer.Sparse.eval]

theorem keyMoment1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1778) =
      Integer.Sparse.eval keyMomentRow1778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3392) := by
    have ha : gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge = raw41191 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41191Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41191 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1778).leftCharge (GramAssembly.key 1778).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1778, Integer.Sparse.eval]

theorem keyMoment1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1779) =
      Integer.Sparse.eval keyMomentRow1779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3376) := by
    have ha : gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge = raw41192 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41192Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41192 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1779).leftCharge (GramAssembly.key 1779).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1779, Integer.Sparse.eval]

theorem keyMoment1780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1780) =
      Integer.Sparse.eval keyMomentRow1780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2603) := by
    have ha : gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge = raw41193 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41193Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41193 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1780).leftCharge (GramAssembly.key 1780).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1780, Integer.Sparse.eval]

theorem keyMoment1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1781) =
      Integer.Sparse.eval keyMomentRow1781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2560) := by
    have ha : gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge = raw41194 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41194Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41194 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1781).leftCharge (GramAssembly.key 1781).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1781, Integer.Sparse.eval]

theorem keyMoment1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1782) =
      Integer.Sparse.eval keyMomentRow1782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3581) := by
    have ha : gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge = raw41195 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41195Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41195 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1782).leftCharge (GramAssembly.key 1782).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1782, Integer.Sparse.eval]

theorem keyMoment1783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1783) =
      Integer.Sparse.eval keyMomentRow1783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3391) := by
    have ha : gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge = raw41196 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41196Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41196 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1783).leftCharge (GramAssembly.key 1783).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1783, Integer.Sparse.eval]

theorem keyMoment1784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1784) =
      Integer.Sparse.eval keyMomentRow1784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3544) := by
    have ha : gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge = raw41197 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41197Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41197 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1784).leftCharge (GramAssembly.key 1784).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1784, Integer.Sparse.eval]

theorem keyMoment1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1785) =
      Integer.Sparse.eval keyMomentRow1785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3622) := by
    have ha : gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge = raw41198 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41198Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41198 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1785).leftCharge (GramAssembly.key 1785).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1785, Integer.Sparse.eval]

theorem keyMoment1786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1786) =
      Integer.Sparse.eval keyMomentRow1786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3533) := by
    have ha : gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge = raw41199 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41199Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41199 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1786).leftCharge (GramAssembly.key 1786).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1786, Integer.Sparse.eval]

theorem keyMoment1787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1787) =
      Integer.Sparse.eval keyMomentRow1787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3390) := by
    have ha : gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge = raw41200 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41200Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41200 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1787).leftCharge (GramAssembly.key 1787).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1787, Integer.Sparse.eval]

theorem keyMoment1788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1788) =
      Integer.Sparse.eval keyMomentRow1788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3532) := by
    have ha : gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge = raw41201 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41201Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41201 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1788).leftCharge (GramAssembly.key 1788).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1788, Integer.Sparse.eval]

theorem keyMoment1789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1789) =
      Integer.Sparse.eval keyMomentRow1789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3118) := by
    have ha : gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge = raw41202 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41202Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41202 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1789).leftCharge (GramAssembly.key 1789).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1789, Integer.Sparse.eval]

theorem keyMoment1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1790) =
      Integer.Sparse.eval keyMomentRow1790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3380) := by
    have ha : gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge = raw41203 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41203Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41203 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1790).leftCharge (GramAssembly.key 1790).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1790, Integer.Sparse.eval]

theorem keyMoment1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1791) =
      Integer.Sparse.eval keyMomentRow1791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge = raw41204 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41204Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41204 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1791).leftCharge (GramAssembly.key 1791).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1791, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
