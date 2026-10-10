import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical322

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1888) =
      Integer.Sparse.eval keyMomentRow1888 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2512) := by
    have ha : gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge = raw41301 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41301Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41301 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1888).leftCharge (GramAssembly.key 1888).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1888, Integer.Sparse.eval]

theorem keyMoment1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1889) =
      Integer.Sparse.eval keyMomentRow1889 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1087) := by
    have ha : gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge = raw41302 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41302Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41302 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1889).leftCharge (GramAssembly.key 1889).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1889, Integer.Sparse.eval]

theorem keyMoment1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1890) =
      Integer.Sparse.eval keyMomentRow1890 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1091) := by
    have ha : gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge = raw41303 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41303Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41303 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1890).leftCharge (GramAssembly.key 1890).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1890, Integer.Sparse.eval]

theorem keyMoment1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1891) =
      Integer.Sparse.eval keyMomentRow1891 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4083) := by
    have ha : gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge = raw41304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41304 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1891).leftCharge (GramAssembly.key 1891).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1891, Integer.Sparse.eval]

theorem keyMoment1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1892) =
      Integer.Sparse.eval keyMomentRow1892 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2741) := by
    have ha : gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge = raw41305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41305 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1892).leftCharge (GramAssembly.key 1892).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1892, Integer.Sparse.eval]

theorem keyMoment1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1893) =
      Integer.Sparse.eval keyMomentRow1893 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3962) := by
    have ha : gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge = raw41306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41306 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1893).leftCharge (GramAssembly.key 1893).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1893, Integer.Sparse.eval]

theorem keyMoment1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1894) =
      Integer.Sparse.eval keyMomentRow1894 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3619) := by
    have ha : gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge = raw41307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41307 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1894).leftCharge (GramAssembly.key 1894).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1894, Integer.Sparse.eval]

theorem keyMoment1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1895) =
      Integer.Sparse.eval keyMomentRow1895 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge = raw41308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41308 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1895).leftCharge (GramAssembly.key 1895).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1895, Integer.Sparse.eval]

theorem keyMoment1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1896) =
      Integer.Sparse.eval keyMomentRow1896 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2263) := by
    have ha : gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge = raw41309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41309 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1896).leftCharge (GramAssembly.key 1896).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1896, Integer.Sparse.eval]

theorem keyMoment1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1897) =
      Integer.Sparse.eval keyMomentRow1897 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge = raw41310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41310 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1897).leftCharge (GramAssembly.key 1897).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1897, Integer.Sparse.eval]

theorem keyMoment1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1898) =
      Integer.Sparse.eval keyMomentRow1898 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge = raw41311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41311 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1898).leftCharge (GramAssembly.key 1898).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1898, Integer.Sparse.eval]

theorem keyMoment1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1899) =
      Integer.Sparse.eval keyMomentRow1899 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3526) := by
    have ha : gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge = raw41312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41312 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1899).leftCharge (GramAssembly.key 1899).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1899, Integer.Sparse.eval]

theorem keyMoment1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1900) =
      Integer.Sparse.eval keyMomentRow1900 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge = raw41313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41313 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1900).leftCharge (GramAssembly.key 1900).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1900, Integer.Sparse.eval]

theorem keyMoment1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1901) =
      Integer.Sparse.eval keyMomentRow1901 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge = raw41314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41314 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1901).leftCharge (GramAssembly.key 1901).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1901, Integer.Sparse.eval]

theorem keyMoment1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1902) =
      Integer.Sparse.eval keyMomentRow1902 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge = raw41315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41315 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1902).leftCharge (GramAssembly.key 1902).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1902, Integer.Sparse.eval]

theorem keyMoment1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1903) =
      Integer.Sparse.eval keyMomentRow1903 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge = raw41316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41316 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1903).leftCharge (GramAssembly.key 1903).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1903, Integer.Sparse.eval]

theorem keyMoment1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1904) =
      Integer.Sparse.eval keyMomentRow1904 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge = raw41317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41317 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1904).leftCharge (GramAssembly.key 1904).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1904, Integer.Sparse.eval]

theorem keyMoment1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1905) =
      Integer.Sparse.eval keyMomentRow1905 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge = raw41318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41318 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1905).leftCharge (GramAssembly.key 1905).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1905, Integer.Sparse.eval]

theorem keyMoment1906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1906) =
      Integer.Sparse.eval keyMomentRow1906 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge = raw41319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41319 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1906).leftCharge (GramAssembly.key 1906).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1906, Integer.Sparse.eval]

theorem keyMoment1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1907) =
      Integer.Sparse.eval keyMomentRow1907 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge = raw41320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41320 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1907).leftCharge (GramAssembly.key 1907).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1907, Integer.Sparse.eval]

theorem keyMoment1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1908) =
      Integer.Sparse.eval keyMomentRow1908 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge = raw41321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41321 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1908).leftCharge (GramAssembly.key 1908).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1908, Integer.Sparse.eval]

theorem keyMoment1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1909) =
      Integer.Sparse.eval keyMomentRow1909 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2277) := by
    have ha : gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge = raw41322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41322 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1909).leftCharge (GramAssembly.key 1909).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1909, Integer.Sparse.eval]

theorem keyMoment1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1910) =
      Integer.Sparse.eval keyMomentRow1910 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge = raw41323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41323 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1910).leftCharge (GramAssembly.key 1910).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1910, Integer.Sparse.eval]

theorem keyMoment1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1911) =
      Integer.Sparse.eval keyMomentRow1911 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3043) := by
    have ha : gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge = raw41324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41324 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1911).leftCharge (GramAssembly.key 1911).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1911, Integer.Sparse.eval]

theorem keyMoment1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1912) =
      Integer.Sparse.eval keyMomentRow1912 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge = raw41325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41325 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1912).leftCharge (GramAssembly.key 1912).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1912, Integer.Sparse.eval]

theorem keyMoment1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1913) =
      Integer.Sparse.eval keyMomentRow1913 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3874) := by
    have ha : gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge = raw41326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41326 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1913).leftCharge (GramAssembly.key 1913).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1913, Integer.Sparse.eval]

theorem keyMoment1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1914) =
      Integer.Sparse.eval keyMomentRow1914 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3488) := by
    have ha : gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge = raw41327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41327 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1914).leftCharge (GramAssembly.key 1914).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1914, Integer.Sparse.eval]

theorem keyMoment1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1915) =
      Integer.Sparse.eval keyMomentRow1915 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge = raw41328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41328 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1915).leftCharge (GramAssembly.key 1915).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1915, Integer.Sparse.eval]

theorem keyMoment1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1916) =
      Integer.Sparse.eval keyMomentRow1916 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2923) := by
    have ha : gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge = raw41329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41329 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1916).leftCharge (GramAssembly.key 1916).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1916, Integer.Sparse.eval]

theorem keyMoment1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1917) =
      Integer.Sparse.eval keyMomentRow1917 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1234) := by
    have ha : gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge = raw41330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41330 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1917).leftCharge (GramAssembly.key 1917).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1917, Integer.Sparse.eval]

theorem keyMoment1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1918) =
      Integer.Sparse.eval keyMomentRow1918 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1233) := by
    have ha : gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge = raw41331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41331 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1918).leftCharge (GramAssembly.key 1918).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1918, Integer.Sparse.eval]

theorem keyMoment1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1919) =
      Integer.Sparse.eval keyMomentRow1919 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1212) := by
    have ha : gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge = raw41332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41332 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1919).leftCharge (GramAssembly.key 1919).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1919, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
