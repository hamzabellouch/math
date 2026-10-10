import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical315
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical316

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 992) =
      Integer.Sparse.eval keyMomentRow992 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3189) := by
    have ha : gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge = raw40432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40432 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow992, Integer.Sparse.eval]

theorem keyMoment993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 993) =
      Integer.Sparse.eval keyMomentRow993 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2800) := by
    have ha : gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge = raw40433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow993, Integer.Sparse.eval]

theorem keyMoment994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 994) =
      Integer.Sparse.eval keyMomentRow994 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3162) := by
    have ha : gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge = raw40434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40434 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow994, Integer.Sparse.eval]

theorem keyMoment995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 995) =
      Integer.Sparse.eval keyMomentRow995 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3199) := by
    have ha : gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge = raw40435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40435 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow995, Integer.Sparse.eval]

theorem keyMoment996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 996) =
      Integer.Sparse.eval keyMomentRow996 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3133) := by
    have ha : gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge = raw40436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40436 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow996, Integer.Sparse.eval]

theorem keyMoment997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 997) =
      Integer.Sparse.eval keyMomentRow997 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge = raw5486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow997, Integer.Sparse.eval]

theorem keyMoment998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 998) =
      Integer.Sparse.eval keyMomentRow998 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2707) := by
    have ha : gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge = raw40437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40437 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow998, Integer.Sparse.eval]

theorem keyMoment999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 999) =
      Integer.Sparse.eval keyMomentRow999 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3155) := by
    have ha : gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge = raw40438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40438 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow999, Integer.Sparse.eval]

theorem keyMoment1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1000) =
      Integer.Sparse.eval keyMomentRow1000 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge = raw40439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1000, Integer.Sparse.eval]

theorem keyMoment1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1001) =
      Integer.Sparse.eval keyMomentRow1001 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3179) := by
    have ha : gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge = raw40440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40440 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1001, Integer.Sparse.eval]

theorem keyMoment1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1002) =
      Integer.Sparse.eval keyMomentRow1002 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3130) := by
    have ha : gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge = raw40441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40441 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1002, Integer.Sparse.eval]

theorem keyMoment1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1003) =
      Integer.Sparse.eval keyMomentRow1003 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3158) := by
    have ha : gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge = raw40442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40442 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1003, Integer.Sparse.eval]

theorem keyMoment1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1004) =
      Integer.Sparse.eval keyMomentRow1004 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2899) := by
    have ha : gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge = raw40443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40443 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1004, Integer.Sparse.eval]

theorem keyMoment1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1005) =
      Integer.Sparse.eval keyMomentRow1005 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3197) := by
    have ha : gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge = raw40444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40444 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1005, Integer.Sparse.eval]

theorem keyMoment1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1006) =
      Integer.Sparse.eval keyMomentRow1006 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2895) := by
    have ha : gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge = raw40445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40445 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1006, Integer.Sparse.eval]

theorem keyMoment1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1007) =
      Integer.Sparse.eval keyMomentRow1007 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3137) := by
    have ha : gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge = raw40446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40446 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1007, Integer.Sparse.eval]

theorem keyMoment1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1008) =
      Integer.Sparse.eval keyMomentRow1008 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2890) := by
    have ha : gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge = raw40447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40447 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1008, Integer.Sparse.eval]

theorem keyMoment1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1009) =
      Integer.Sparse.eval keyMomentRow1009 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3128) := by
    have ha : gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge = raw40448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40448 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1009, Integer.Sparse.eval]

theorem keyMoment1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1010) =
      Integer.Sparse.eval keyMomentRow1010 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3172) := by
    have ha : gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge = raw40449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40449 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1010, Integer.Sparse.eval]

theorem keyMoment1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1011) =
      Integer.Sparse.eval keyMomentRow1011 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2520) := by
    have ha : gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge = raw40450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1011, Integer.Sparse.eval]

theorem keyMoment1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1012) =
      Integer.Sparse.eval keyMomentRow1012 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1146) := by
    have ha : gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge = raw40451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1012, Integer.Sparse.eval]

theorem keyMoment1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1013) =
      Integer.Sparse.eval keyMomentRow1013 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2497) := by
    have ha : gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge = raw40452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1013, Integer.Sparse.eval]

theorem keyMoment1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1014) =
      Integer.Sparse.eval keyMomentRow1014 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1137) := by
    have ha : gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge = raw40453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1014, Integer.Sparse.eval]

theorem keyMoment1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1015) =
      Integer.Sparse.eval keyMomentRow1015 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2443) := by
    have ha : gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge = raw40454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1015, Integer.Sparse.eval]

theorem keyMoment1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1016) =
      Integer.Sparse.eval keyMomentRow1016 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1121) := by
    have ha : gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge = raw40455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1016, Integer.Sparse.eval]

theorem keyMoment1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1017) =
      Integer.Sparse.eval keyMomentRow1017 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2435) := by
    have ha : gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge = raw40456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1017, Integer.Sparse.eval]

theorem keyMoment1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1018) =
      Integer.Sparse.eval keyMomentRow1018 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2486) := by
    have ha : gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge = raw40457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1018, Integer.Sparse.eval]

theorem keyMoment1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1019) =
      Integer.Sparse.eval keyMomentRow1019 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3132) := by
    have ha : gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge = raw40458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1019, Integer.Sparse.eval]

theorem keyMoment1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1020) =
      Integer.Sparse.eval keyMomentRow1020 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2440) := by
    have ha : gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge = raw40459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1020, Integer.Sparse.eval]

theorem keyMoment1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1021) =
      Integer.Sparse.eval keyMomentRow1021 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1116) := by
    have ha : gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge = raw40460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1021, Integer.Sparse.eval]

theorem keyMoment1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1022) =
      Integer.Sparse.eval keyMomentRow1022 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2430) := by
    have ha : gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge = raw40461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1022, Integer.Sparse.eval]

theorem keyMoment1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1023) =
      Integer.Sparse.eval keyMomentRow1023 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2471) := by
    have ha : gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge = raw40462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1023, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
