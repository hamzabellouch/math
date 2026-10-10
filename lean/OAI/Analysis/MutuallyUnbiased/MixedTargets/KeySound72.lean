import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical327

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2304) =
      Integer.Sparse.eval keyMomentRow2304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1720) := by
    have ha : gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge = raw41920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41920 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4367) := by
    have ha : gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge = raw41921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41921 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2304).leftCharge (GramAssembly.key 2304).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2304, Integer.Sparse.eval]; ring

theorem keyMoment2305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2305) =
      Integer.Sparse.eval keyMomentRow2305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1723) := by
    have ha : gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge = raw41922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41922 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4440) := by
    have ha : gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge = raw41923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41923 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2305).leftCharge (GramAssembly.key 2305).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2305, Integer.Sparse.eval]; ring

theorem keyMoment2306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2306) =
      Integer.Sparse.eval keyMomentRow2306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1721) := by
    have ha : gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge = raw41924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41924 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4369) := by
    have ha : gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge = raw41925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41925 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2306).leftCharge (GramAssembly.key 2306).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2306, Integer.Sparse.eval]; ring

theorem keyMoment2307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2307) =
      Integer.Sparse.eval keyMomentRow2307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1670) := by
    have ha : gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge = raw41926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41926 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4327) := by
    have ha : gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge = raw41927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41927 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2307).leftCharge (GramAssembly.key 2307).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2307, Integer.Sparse.eval]; ring

theorem keyMoment2308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2308) =
      Integer.Sparse.eval keyMomentRow2308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1757) := by
    have ha : gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge = raw41928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41928 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4481) := by
    have ha : gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge = raw41929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41929 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2308).leftCharge (GramAssembly.key 2308).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2308, Integer.Sparse.eval]; ring

theorem keyMoment2309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2309) =
      Integer.Sparse.eval keyMomentRow2309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1540) := by
    have ha : gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge = raw41930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41930 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4189) := by
    have ha : gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge = raw41931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41931 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2309).leftCharge (GramAssembly.key 2309).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2309, Integer.Sparse.eval]; ring

theorem keyMoment2310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2310) =
      Integer.Sparse.eval keyMomentRow2310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1532) := by
    have ha : gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge = raw41932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41932 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4159) := by
    have ha : gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge = raw41933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41933 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2310).leftCharge (GramAssembly.key 2310).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2310, Integer.Sparse.eval]; ring

theorem keyMoment2311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2311) =
      Integer.Sparse.eval keyMomentRow2311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1695) := by
    have ha : gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge = raw41934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41934 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4358) := by
    have ha : gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge = raw41935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41935 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2311).leftCharge (GramAssembly.key 2311).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2311, Integer.Sparse.eval]; ring

theorem keyMoment2312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2312) =
      Integer.Sparse.eval keyMomentRow2312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1749) := by
    have ha : gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge = raw41936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41936 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4445) := by
    have ha : gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge = raw41937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41937 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2312).leftCharge (GramAssembly.key 2312).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2312, Integer.Sparse.eval]; ring

theorem keyMoment2313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2313) =
      Integer.Sparse.eval keyMomentRow2313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1748) := by
    have ha : gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge = raw41938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41938 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4374) := by
    have ha : gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge = raw41939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41939 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2313).leftCharge (GramAssembly.key 2313).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2313, Integer.Sparse.eval]; ring

theorem keyMoment2314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2314) =
      Integer.Sparse.eval keyMomentRow2314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1688) := by
    have ha : gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge = raw41940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41940 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4333) := by
    have ha : gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge = raw41941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41941 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2314).leftCharge (GramAssembly.key 2314).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2314, Integer.Sparse.eval]; ring

theorem keyMoment2315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2315) =
      Integer.Sparse.eval keyMomentRow2315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1689) := by
    have ha : gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge = raw41942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41942 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4335) := by
    have ha : gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge = raw41943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41943 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2315).leftCharge (GramAssembly.key 2315).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2315, Integer.Sparse.eval]; ring

theorem keyMoment2316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2316) =
      Integer.Sparse.eval keyMomentRow2316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1529) := by
    have ha : gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge = raw41944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41944 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4162) := by
    have ha : gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge = raw41945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41945 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2316).leftCharge (GramAssembly.key 2316).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2316, Integer.Sparse.eval]; ring

theorem keyMoment2317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2317) =
      Integer.Sparse.eval keyMomentRow2317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1528) := by
    have ha : gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge = raw41946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41946 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4157) := by
    have ha : gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge = raw41947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41947 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2317).leftCharge (GramAssembly.key 2317).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2317, Integer.Sparse.eval]; ring

theorem keyMoment2318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2318) =
      Integer.Sparse.eval keyMomentRow2318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1511) := by
    have ha : gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge = raw41948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41948 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4154) := by
    have ha : gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge = raw41949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41949 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2318).leftCharge (GramAssembly.key 2318).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2318, Integer.Sparse.eval]; ring

theorem keyMoment2319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2319) =
      Integer.Sparse.eval keyMomentRow2319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1510) := by
    have ha : gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge = raw41950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41950 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4152) := by
    have ha : gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge = raw41951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41951 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2319).leftCharge (GramAssembly.key 2319).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2319, Integer.Sparse.eval]; ring

theorem keyMoment2320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2320) =
      Integer.Sparse.eval keyMomentRow2320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1523) := by
    have ha : gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge = raw41952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41952 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4160) := by
    have ha : gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge = raw41953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41953 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2320).leftCharge (GramAssembly.key 2320).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2320, Integer.Sparse.eval]; ring

theorem keyMoment2321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2321) =
      Integer.Sparse.eval keyMomentRow2321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1522) := by
    have ha : gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge = raw41954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41954 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4158) := by
    have ha : gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge = raw41955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41955 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2321).leftCharge (GramAssembly.key 2321).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2321, Integer.Sparse.eval]; ring

theorem keyMoment2322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2322) =
      Integer.Sparse.eval keyMomentRow2322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1501) := by
    have ha : gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge = raw41956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41956 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4149) := by
    have ha : gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge = raw41957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41957 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2322).leftCharge (GramAssembly.key 2322).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2322, Integer.Sparse.eval]; ring

theorem keyMoment2323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2323) =
      Integer.Sparse.eval keyMomentRow2323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1505) := by
    have ha : gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge = raw41958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41958 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4151) := by
    have ha : gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge = raw41959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41959 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2323).leftCharge (GramAssembly.key 2323).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2323, Integer.Sparse.eval]; ring

theorem keyMoment2324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2324) =
      Integer.Sparse.eval keyMomentRow2324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1504) := by
    have ha : gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge = raw41960 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41960Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41960 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4150) := by
    have ha : gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge = raw41961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41961 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2324).leftCharge (GramAssembly.key 2324).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2324, Integer.Sparse.eval]; ring

theorem keyMoment2325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2325) =
      Integer.Sparse.eval keyMomentRow2325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1516) := by
    have ha : gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge = raw41962 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41962Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41962 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4156) := by
    have ha : gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge = raw41963 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41963Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41963 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2325).leftCharge (GramAssembly.key 2325).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2325, Integer.Sparse.eval]; ring

theorem keyMoment2326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2326) =
      Integer.Sparse.eval keyMomentRow2326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1514) := by
    have ha : gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge = raw41964 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41964Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41964 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4153) := by
    have ha : gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge = raw41965 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41965Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41965 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2326).leftCharge (GramAssembly.key 2326).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2326, Integer.Sparse.eval]; ring

theorem keyMoment2327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2327) =
      Integer.Sparse.eval keyMomentRow2327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1515) := by
    have ha : gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge = raw41966 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41966Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41966 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4155) := by
    have ha : gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge = raw41967 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41967Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41967 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2327).leftCharge (GramAssembly.key 2327).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2327, Integer.Sparse.eval]; ring

theorem keyMoment2328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2328) =
      Integer.Sparse.eval keyMomentRow2328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1534) := by
    have ha : gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge = raw41968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41968 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4163) := by
    have ha : gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge = raw41969 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41969Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41969 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2328).leftCharge (GramAssembly.key 2328).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2328, Integer.Sparse.eval]; ring

theorem keyMoment2329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2329) =
      Integer.Sparse.eval keyMomentRow2329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1532) := by
    have ha : gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge = raw41970 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41970Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41970 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4159) := by
    have ha : gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge = raw41971 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41971Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41971 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2329).leftCharge (GramAssembly.key 2329).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2329, Integer.Sparse.eval]; ring

theorem keyMoment2330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2330) =
      Integer.Sparse.eval keyMomentRow2330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1533) := by
    have ha : gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge = raw41972 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41972Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41972 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4161) := by
    have ha : gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge = raw41973 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41973Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41973 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2330).leftCharge (GramAssembly.key 2330).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2330, Integer.Sparse.eval]; ring

theorem keyMoment2331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2331) =
      Integer.Sparse.eval keyMomentRow2331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3114) := by
    have ha : gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge = raw41974 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41974Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41974 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4897) := by
    have ha : gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge = raw41975 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41975Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41975 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2331).leftCharge (GramAssembly.key 2331).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2331, Integer.Sparse.eval]; ring

theorem keyMoment2332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2332) =
      Integer.Sparse.eval keyMomentRow2332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3112) := by
    have ha : gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge = raw41976 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41976Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41976 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5274) := by
    have ha : gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge = raw41977 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41977Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41977 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2332).leftCharge (GramAssembly.key 2332).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2332, Integer.Sparse.eval]; ring

theorem keyMoment2333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2333) =
      Integer.Sparse.eval keyMomentRow2333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3110) := by
    have ha : gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge = raw41978 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41978Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41978 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5275) := by
    have ha : gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge = raw41979 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41979Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41979 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2333).leftCharge (GramAssembly.key 2333).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2333, Integer.Sparse.eval]; ring

theorem keyMoment2334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2334) =
      Integer.Sparse.eval keyMomentRow2334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge = raw41980 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41980Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41980 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge = raw41981 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41981Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41981 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2334).leftCharge (GramAssembly.key 2334).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2334, Integer.Sparse.eval]; ring

theorem keyMoment2335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2335) =
      Integer.Sparse.eval keyMomentRow2335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3089) := by
    have ha : gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge = raw41982 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41982Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41982 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5258) := by
    have ha : gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge = raw41983 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41983Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41983 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2335).leftCharge (GramAssembly.key 2335).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2335, Integer.Sparse.eval]; ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
