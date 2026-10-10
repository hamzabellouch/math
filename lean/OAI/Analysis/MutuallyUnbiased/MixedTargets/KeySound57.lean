import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical322

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1824) =
      Integer.Sparse.eval keyMomentRow1824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4049) := by
    have ha : gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge = raw41237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41237 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1824).leftCharge (GramAssembly.key 1824).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1824, Integer.Sparse.eval]

theorem keyMoment1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1825) =
      Integer.Sparse.eval keyMomentRow1825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge = raw41238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41238 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1825).leftCharge (GramAssembly.key 1825).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1825, Integer.Sparse.eval]

theorem keyMoment1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1826) =
      Integer.Sparse.eval keyMomentRow1826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge = raw41239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41239 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1826).leftCharge (GramAssembly.key 1826).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1826, Integer.Sparse.eval]

theorem keyMoment1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1827) =
      Integer.Sparse.eval keyMomentRow1827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4047) := by
    have ha : gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge = raw41240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41240 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1827).leftCharge (GramAssembly.key 1827).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1827, Integer.Sparse.eval]

theorem keyMoment1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1828) =
      Integer.Sparse.eval keyMomentRow1828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4048) := by
    have ha : gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge = raw41241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41241 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1828).leftCharge (GramAssembly.key 1828).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1828, Integer.Sparse.eval]

theorem keyMoment1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1829) =
      Integer.Sparse.eval keyMomentRow1829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge = raw41242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41242 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1829).leftCharge (GramAssembly.key 1829).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1829, Integer.Sparse.eval]

theorem keyMoment1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1830) =
      Integer.Sparse.eval keyMomentRow1830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge = raw41243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41243 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1830).leftCharge (GramAssembly.key 1830).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1830, Integer.Sparse.eval]

theorem keyMoment1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1831) =
      Integer.Sparse.eval keyMomentRow1831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4046) := by
    have ha : gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge = raw41244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41244 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1831).leftCharge (GramAssembly.key 1831).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1831, Integer.Sparse.eval]

theorem keyMoment1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1832) =
      Integer.Sparse.eval keyMomentRow1832 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2262) := by
    have ha : gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge = raw41245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41245 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1832).leftCharge (GramAssembly.key 1832).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1832, Integer.Sparse.eval]

theorem keyMoment1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1833) =
      Integer.Sparse.eval keyMomentRow1833 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2720) := by
    have ha : gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge = raw41246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41246 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1833).leftCharge (GramAssembly.key 1833).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1833, Integer.Sparse.eval]

theorem keyMoment1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1834) =
      Integer.Sparse.eval keyMomentRow1834 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3036) := by
    have ha : gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge = raw41247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41247 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1834).leftCharge (GramAssembly.key 1834).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1834, Integer.Sparse.eval]

theorem keyMoment1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1835) =
      Integer.Sparse.eval keyMomentRow1835 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge = raw41248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41248 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1835).leftCharge (GramAssembly.key 1835).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1835, Integer.Sparse.eval]

theorem keyMoment1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1836) =
      Integer.Sparse.eval keyMomentRow1836 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3956) := by
    have ha : gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge = raw41249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41249 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1836).leftCharge (GramAssembly.key 1836).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1836, Integer.Sparse.eval]

theorem keyMoment1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1837) =
      Integer.Sparse.eval keyMomentRow1837 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3497) := by
    have ha : gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge = raw41250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41250 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1837).leftCharge (GramAssembly.key 1837).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1837, Integer.Sparse.eval]

theorem keyMoment1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1838) =
      Integer.Sparse.eval keyMomentRow1838 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2879) := by
    have ha : gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge = raw41251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41251 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1838).leftCharge (GramAssembly.key 1838).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1838, Integer.Sparse.eval]

theorem keyMoment1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1839) =
      Integer.Sparse.eval keyMomentRow1839 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2878) := by
    have ha : gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge = raw41252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41252 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1839).leftCharge (GramAssembly.key 1839).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1839, Integer.Sparse.eval]

theorem keyMoment1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1840) =
      Integer.Sparse.eval keyMomentRow1840 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2861) := by
    have ha : gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge = raw41253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41253 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1840).leftCharge (GramAssembly.key 1840).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1840, Integer.Sparse.eval]

theorem keyMoment1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1841) =
      Integer.Sparse.eval keyMomentRow1841 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2763) := by
    have ha : gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge = raw41254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41254 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1841).leftCharge (GramAssembly.key 1841).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1841, Integer.Sparse.eval]

theorem keyMoment1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1842) =
      Integer.Sparse.eval keyMomentRow1842 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3084) := by
    have ha : gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge = raw41255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41255 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1842).leftCharge (GramAssembly.key 1842).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1842, Integer.Sparse.eval]

theorem keyMoment1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1843) =
      Integer.Sparse.eval keyMomentRow1843 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3978) := by
    have ha : gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge = raw41256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41256 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1843).leftCharge (GramAssembly.key 1843).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1843, Integer.Sparse.eval]

theorem keyMoment1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1844) =
      Integer.Sparse.eval keyMomentRow1844 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3946) := by
    have ha : gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge = raw41257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41257 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1844).leftCharge (GramAssembly.key 1844).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1844, Integer.Sparse.eval]

theorem keyMoment1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1845) =
      Integer.Sparse.eval keyMomentRow1845 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2882) := by
    have ha : gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge = raw41258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41258 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1845).leftCharge (GramAssembly.key 1845).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1845, Integer.Sparse.eval]

theorem keyMoment1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1846) =
      Integer.Sparse.eval keyMomentRow1846 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2862) := by
    have ha : gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge = raw41259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41259 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1846).leftCharge (GramAssembly.key 1846).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1846, Integer.Sparse.eval]

theorem keyMoment1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1847) =
      Integer.Sparse.eval keyMomentRow1847 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2600) := by
    have ha : gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge = raw41260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41260 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1847).leftCharge (GramAssembly.key 1847).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1847, Integer.Sparse.eval]

theorem keyMoment1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1848) =
      Integer.Sparse.eval keyMomentRow1848 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2557) := by
    have ha : gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge = raw41261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41261 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1848).leftCharge (GramAssembly.key 1848).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1848, Integer.Sparse.eval]

theorem keyMoment1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1849) =
      Integer.Sparse.eval keyMomentRow1849 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2558) := by
    have ha : gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge = raw41262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41262 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1849).leftCharge (GramAssembly.key 1849).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1849, Integer.Sparse.eval]

theorem keyMoment1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1850) =
      Integer.Sparse.eval keyMomentRow1850 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge = raw41263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41263 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1850).leftCharge (GramAssembly.key 1850).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1850, Integer.Sparse.eval]

theorem keyMoment1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1851) =
      Integer.Sparse.eval keyMomentRow1851 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3857) := by
    have ha : gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge = raw41264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41264 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1851).leftCharge (GramAssembly.key 1851).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1851, Integer.Sparse.eval]

theorem keyMoment1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1852) =
      Integer.Sparse.eval keyMomentRow1852 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2058) := by
    have ha : gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge = raw41265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41265 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1852).leftCharge (GramAssembly.key 1852).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1852, Integer.Sparse.eval]

theorem keyMoment1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1853) =
      Integer.Sparse.eval keyMomentRow1853 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3544) := by
    have ha : gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge = raw41266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41266 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1853).leftCharge (GramAssembly.key 1853).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1853, Integer.Sparse.eval]

theorem keyMoment1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1854) =
      Integer.Sparse.eval keyMomentRow1854 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4047) := by
    have ha : gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge = raw41267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41267 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1854).leftCharge (GramAssembly.key 1854).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1854, Integer.Sparse.eval]

theorem keyMoment1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1855) =
      Integer.Sparse.eval keyMomentRow1855 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4008) := by
    have ha : gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge = raw41268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41268 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1855).leftCharge (GramAssembly.key 1855).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1855, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
