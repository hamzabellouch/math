import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical322

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1856) =
      Integer.Sparse.eval keyMomentRow1856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3782) := by
    have ha : gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge = raw41269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41269 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1856, Integer.Sparse.eval]

theorem keyMoment1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1857) =
      Integer.Sparse.eval keyMomentRow1857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4044) := by
    have ha : gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge = raw41270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41270 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1857, Integer.Sparse.eval]

theorem keyMoment1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1858) =
      Integer.Sparse.eval keyMomentRow1858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4046) := by
    have ha : gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge = raw41271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41271 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1858, Integer.Sparse.eval]

theorem keyMoment1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1859) =
      Integer.Sparse.eval keyMomentRow1859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge = raw41272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41272 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1859, Integer.Sparse.eval]

theorem keyMoment1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1860) =
      Integer.Sparse.eval keyMomentRow1860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2881) := by
    have ha : gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge = raw41273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41273 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1860, Integer.Sparse.eval]

theorem keyMoment1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1861) =
      Integer.Sparse.eval keyMomentRow1861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge = raw41274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41274 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1861, Integer.Sparse.eval]

theorem keyMoment1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1862) =
      Integer.Sparse.eval keyMomentRow1862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge = raw41275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41275 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1862, Integer.Sparse.eval]

theorem keyMoment1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1863) =
      Integer.Sparse.eval keyMomentRow1863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2880) := by
    have ha : gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge = raw41276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41276 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1863, Integer.Sparse.eval]

theorem keyMoment1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1864) =
      Integer.Sparse.eval keyMomentRow1864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge = raw41277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41277 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1864, Integer.Sparse.eval]

theorem keyMoment1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1865) =
      Integer.Sparse.eval keyMomentRow1865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3108) := by
    have ha : gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge = raw41278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1865, Integer.Sparse.eval]

theorem keyMoment1866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1866) =
      Integer.Sparse.eval keyMomentRow1866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3922) := by
    have ha : gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge = raw41279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41279 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1866, Integer.Sparse.eval]

theorem keyMoment1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1867) =
      Integer.Sparse.eval keyMomentRow1867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2868) := by
    have ha : gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge = raw41280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41280 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1867, Integer.Sparse.eval]

theorem keyMoment1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1868) =
      Integer.Sparse.eval keyMomentRow1868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge = raw41281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41281 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1868, Integer.Sparse.eval]

theorem keyMoment1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1869) =
      Integer.Sparse.eval keyMomentRow1869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3983) := by
    have ha : gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge = raw41282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41282 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1869, Integer.Sparse.eval]

theorem keyMoment1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1870) =
      Integer.Sparse.eval keyMomentRow1870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3706) := by
    have ha : gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge = raw41283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41283 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1870, Integer.Sparse.eval]

theorem keyMoment1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1871) =
      Integer.Sparse.eval keyMomentRow1871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge = raw41284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41284 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1871, Integer.Sparse.eval]

theorem keyMoment1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1872) =
      Integer.Sparse.eval keyMomentRow1872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge = raw41285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41285 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1872, Integer.Sparse.eval]

theorem keyMoment1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1873) =
      Integer.Sparse.eval keyMomentRow1873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3964) := by
    have ha : gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge = raw41286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41286 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1873, Integer.Sparse.eval]

theorem keyMoment1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1874) =
      Integer.Sparse.eval keyMomentRow1874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge = raw41287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41287 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1874, Integer.Sparse.eval]

theorem keyMoment1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1875) =
      Integer.Sparse.eval keyMomentRow1875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3703) := by
    have ha : gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge = raw41288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41288 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1875, Integer.Sparse.eval]

theorem keyMoment1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1876) =
      Integer.Sparse.eval keyMomentRow1876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2889) := by
    have ha : gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge = raw41289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41289 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1876, Integer.Sparse.eval]

theorem keyMoment1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1877) =
      Integer.Sparse.eval keyMomentRow1877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3963) := by
    have ha : gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge = raw41290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41290 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1877, Integer.Sparse.eval]

theorem keyMoment1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1878) =
      Integer.Sparse.eval keyMomentRow1878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2884) := by
    have ha : gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge = raw41291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41291 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1878, Integer.Sparse.eval]

theorem keyMoment1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1879) =
      Integer.Sparse.eval keyMomentRow1879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge = raw41292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41292 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1879, Integer.Sparse.eval]

theorem keyMoment1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1880) =
      Integer.Sparse.eval keyMomentRow1880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3705) := by
    have ha : gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge = raw41293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41293 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1880, Integer.Sparse.eval]

theorem keyMoment1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1881) =
      Integer.Sparse.eval keyMomentRow1881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3945) := by
    have ha : gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge = raw41294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41294 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1881, Integer.Sparse.eval]

theorem keyMoment1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1882) =
      Integer.Sparse.eval keyMomentRow1882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge = raw41295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41295 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1882, Integer.Sparse.eval]

theorem keyMoment1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1883) =
      Integer.Sparse.eval keyMomentRow1883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2515) := by
    have ha : gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge = raw41296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41296 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1883, Integer.Sparse.eval]

theorem keyMoment1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1884) =
      Integer.Sparse.eval keyMomentRow1884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge = raw41297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41297 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1884, Integer.Sparse.eval]

theorem keyMoment1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1885) =
      Integer.Sparse.eval keyMomentRow1885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2508) := by
    have ha : gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge = raw41298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1885, Integer.Sparse.eval]

theorem keyMoment1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1886) =
      Integer.Sparse.eval keyMomentRow1886 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2519) := by
    have ha : gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge = raw41299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41299 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1886, Integer.Sparse.eval]

theorem keyMoment1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1887) =
      Integer.Sparse.eval keyMomentRow1887 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge = raw41300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41300 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1887, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
