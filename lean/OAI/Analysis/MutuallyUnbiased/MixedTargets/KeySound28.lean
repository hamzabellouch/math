import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 896) =
      Integer.Sparse.eval keyMomentRow896 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge = raw40337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40337 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow896, Integer.Sparse.eval]

theorem keyMoment897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 897) =
      Integer.Sparse.eval keyMomentRow897 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge = raw40338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40338 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow897, Integer.Sparse.eval]

theorem keyMoment898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 898) =
      Integer.Sparse.eval keyMomentRow898 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge = raw40339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40339 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow898, Integer.Sparse.eval]

theorem keyMoment899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 899) =
      Integer.Sparse.eval keyMomentRow899 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3056) := by
    have ha : gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge = raw40340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40340 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow899, Integer.Sparse.eval]

theorem keyMoment900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 900) =
      Integer.Sparse.eval keyMomentRow900 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3031) := by
    have ha : gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge = raw40341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40341 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow900, Integer.Sparse.eval]

theorem keyMoment901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 901) =
      Integer.Sparse.eval keyMomentRow901 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge = raw40342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40342 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow901, Integer.Sparse.eval]

theorem keyMoment902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 902) =
      Integer.Sparse.eval keyMomentRow902 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge = raw40343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40343 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow902, Integer.Sparse.eval]

theorem keyMoment903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 903) =
      Integer.Sparse.eval keyMomentRow903 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3040) := by
    have ha : gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge = raw40344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40344 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow903, Integer.Sparse.eval]

theorem keyMoment904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 904) =
      Integer.Sparse.eval keyMomentRow904 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3044) := by
    have ha : gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge = raw40345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40345 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow904, Integer.Sparse.eval]

theorem keyMoment905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 905) =
      Integer.Sparse.eval keyMomentRow905 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3045) := by
    have ha : gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge = raw40346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40346 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow905, Integer.Sparse.eval]

theorem keyMoment906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 906) =
      Integer.Sparse.eval keyMomentRow906 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3050) := by
    have ha : gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge = raw40347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40347 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow906, Integer.Sparse.eval]

theorem keyMoment907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 907) =
      Integer.Sparse.eval keyMomentRow907 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge = raw40348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40348 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow907, Integer.Sparse.eval]

theorem keyMoment908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 908) =
      Integer.Sparse.eval keyMomentRow908 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3053) := by
    have ha : gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge = raw40349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40349 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow908, Integer.Sparse.eval]

theorem keyMoment909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 909) =
      Integer.Sparse.eval keyMomentRow909 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3029) := by
    have ha : gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge = raw40350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40350 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow909, Integer.Sparse.eval]

theorem keyMoment910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 910) =
      Integer.Sparse.eval keyMomentRow910 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3030) := by
    have ha : gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge = raw40351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40351 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow910, Integer.Sparse.eval]

theorem keyMoment911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 911) =
      Integer.Sparse.eval keyMomentRow911 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3036) := by
    have ha : gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge = raw40352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40352 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow911, Integer.Sparse.eval]

theorem keyMoment912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 912) =
      Integer.Sparse.eval keyMomentRow912 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge = raw40353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40353 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow912, Integer.Sparse.eval]

theorem keyMoment913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 913) =
      Integer.Sparse.eval keyMomentRow913 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3043) := by
    have ha : gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge = raw40354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40354 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow913, Integer.Sparse.eval]

theorem keyMoment914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 914) =
      Integer.Sparse.eval keyMomentRow914 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge = raw40355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40355 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow914, Integer.Sparse.eval]

theorem keyMoment915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 915) =
      Integer.Sparse.eval keyMomentRow915 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge = raw40356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40356 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow915, Integer.Sparse.eval]

theorem keyMoment916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 916) =
      Integer.Sparse.eval keyMomentRow916 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge = raw13433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw13433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical13433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow916, Integer.Sparse.eval]

theorem keyMoment917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 917) =
      Integer.Sparse.eval keyMomentRow917 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge = raw40357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40357 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow917, Integer.Sparse.eval]

theorem keyMoment918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 918) =
      Integer.Sparse.eval keyMomentRow918 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3079) := by
    have ha : gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge = raw40358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40358 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow918, Integer.Sparse.eval]

theorem keyMoment919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 919) =
      Integer.Sparse.eval keyMomentRow919 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge = raw40359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40359 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow919, Integer.Sparse.eval]

theorem keyMoment920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 920) =
      Integer.Sparse.eval keyMomentRow920 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3066) := by
    have ha : gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge = raw40360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40360 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow920, Integer.Sparse.eval]

theorem keyMoment921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 921) =
      Integer.Sparse.eval keyMomentRow921 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3068) := by
    have ha : gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge = raw40361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40361 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow921, Integer.Sparse.eval]

theorem keyMoment922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 922) =
      Integer.Sparse.eval keyMomentRow922 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3069) := by
    have ha : gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge = raw40362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40362 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow922, Integer.Sparse.eval]

theorem keyMoment923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 923) =
      Integer.Sparse.eval keyMomentRow923 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3073) := by
    have ha : gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge = raw40363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40363 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow923, Integer.Sparse.eval]

theorem keyMoment924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 924) =
      Integer.Sparse.eval keyMomentRow924 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge = raw40364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40364 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow924, Integer.Sparse.eval]

theorem keyMoment925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 925) =
      Integer.Sparse.eval keyMomentRow925 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge = raw40365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40365 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow925, Integer.Sparse.eval]

theorem keyMoment926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 926) =
      Integer.Sparse.eval keyMomentRow926 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2967) := by
    have ha : gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge = raw40366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40366 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow926, Integer.Sparse.eval]

theorem keyMoment927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 927) =
      Integer.Sparse.eval keyMomentRow927 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge = raw40367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40367 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow927, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
