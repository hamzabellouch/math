import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical323

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1984) =
      Integer.Sparse.eval keyMomentRow1984 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1125) := by
    have ha : gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge = raw41397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41397 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1984).leftCharge (GramAssembly.key 1984).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1984, Integer.Sparse.eval]

theorem keyMoment1985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1985) =
      Integer.Sparse.eval keyMomentRow1985 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 597) := by
    have ha : gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge = raw41398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41398 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1985).leftCharge (GramAssembly.key 1985).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1985, Integer.Sparse.eval]

theorem keyMoment1986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1986) =
      Integer.Sparse.eval keyMomentRow1986 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 577) := by
    have ha : gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge = raw41399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41399 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1986).leftCharge (GramAssembly.key 1986).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1986, Integer.Sparse.eval]

theorem keyMoment1987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1987) =
      Integer.Sparse.eval keyMomentRow1987 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2132) := by
    have ha : gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge = raw41400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41400 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1987).leftCharge (GramAssembly.key 1987).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1987, Integer.Sparse.eval]

theorem keyMoment1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1988) =
      Integer.Sparse.eval keyMomentRow1988 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1822) := by
    have ha : gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge = raw41401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41401 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1988).leftCharge (GramAssembly.key 1988).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1988, Integer.Sparse.eval]

theorem keyMoment1989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1989) =
      Integer.Sparse.eval keyMomentRow1989 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2088) := by
    have ha : gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge = raw41402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41402 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1989).leftCharge (GramAssembly.key 1989).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1989, Integer.Sparse.eval]

theorem keyMoment1990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1990) =
      Integer.Sparse.eval keyMomentRow1990 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1803) := by
    have ha : gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge = raw41403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41403 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1990).leftCharge (GramAssembly.key 1990).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1990, Integer.Sparse.eval]

theorem keyMoment1991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1991) =
      Integer.Sparse.eval keyMomentRow1991 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 601) := by
    have ha : gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge = raw41404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41404 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1991).leftCharge (GramAssembly.key 1991).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1991, Integer.Sparse.eval]

theorem keyMoment1992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1992) =
      Integer.Sparse.eval keyMomentRow1992 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 578) := by
    have ha : gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge = raw41405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1992).leftCharge (GramAssembly.key 1992).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1992, Integer.Sparse.eval]

theorem keyMoment1993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1993) =
      Integer.Sparse.eval keyMomentRow1993 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1823) := by
    have ha : gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge = raw41406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41406 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1993).leftCharge (GramAssembly.key 1993).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1993, Integer.Sparse.eval]

theorem keyMoment1994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1994) =
      Integer.Sparse.eval keyMomentRow1994 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1789) := by
    have ha : gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge = raw41407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41407 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1994).leftCharge (GramAssembly.key 1994).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1994, Integer.Sparse.eval]

theorem keyMoment1995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1995) =
      Integer.Sparse.eval keyMomentRow1995 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2529) := by
    have ha : gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge = raw41408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41408 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1995).leftCharge (GramAssembly.key 1995).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1995, Integer.Sparse.eval]

theorem keyMoment1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1996) =
      Integer.Sparse.eval keyMomentRow1996 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2524) := by
    have ha : gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge = raw41409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41409 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1996).leftCharge (GramAssembly.key 1996).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1996, Integer.Sparse.eval]

theorem keyMoment1997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1997) =
      Integer.Sparse.eval keyMomentRow1997 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1111) := by
    have ha : gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge = raw41410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41410 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1997).leftCharge (GramAssembly.key 1997).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1997, Integer.Sparse.eval]

theorem keyMoment1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1998) =
      Integer.Sparse.eval keyMomentRow1998 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 579) := by
    have ha : gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge = raw41411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41411 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1998).leftCharge (GramAssembly.key 1998).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1998, Integer.Sparse.eval]

theorem keyMoment1999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1999) =
      Integer.Sparse.eval keyMomentRow1999 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2105) := by
    have ha : gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge = raw41412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41412 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1999).leftCharge (GramAssembly.key 1999).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1999, Integer.Sparse.eval]

theorem keyMoment2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2000) =
      Integer.Sparse.eval keyMomentRow2000 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1802) := by
    have ha : gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge = raw41413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41413 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2000).leftCharge (GramAssembly.key 2000).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2000, Integer.Sparse.eval]

theorem keyMoment2001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2001) =
      Integer.Sparse.eval keyMomentRow2001 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2051) := by
    have ha : gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge = raw41414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41414 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2001).leftCharge (GramAssembly.key 2001).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2001, Integer.Sparse.eval]

theorem keyMoment2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2002) =
      Integer.Sparse.eval keyMomentRow2002 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2243) := by
    have ha : gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge = raw41415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41415 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2002).leftCharge (GramAssembly.key 2002).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2002, Integer.Sparse.eval]

theorem keyMoment2003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2003) =
      Integer.Sparse.eval keyMomentRow2003 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2019) := by
    have ha : gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge = raw41416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41416 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2003).leftCharge (GramAssembly.key 2003).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2003, Integer.Sparse.eval]

theorem keyMoment2004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2004) =
      Integer.Sparse.eval keyMomentRow2004 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3812) := by
    have ha : gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge = raw41417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41417 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2004).leftCharge (GramAssembly.key 2004).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2004, Integer.Sparse.eval]

theorem keyMoment2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2005) =
      Integer.Sparse.eval keyMomentRow2005 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3786) := by
    have ha : gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge = raw41418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41418 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2005).leftCharge (GramAssembly.key 2005).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2005, Integer.Sparse.eval]

theorem keyMoment2006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2006) =
      Integer.Sparse.eval keyMomentRow2006 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1966) := by
    have ha : gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge = raw41419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41419 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2006).leftCharge (GramAssembly.key 2006).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2006, Integer.Sparse.eval]

theorem keyMoment2007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2007) =
      Integer.Sparse.eval keyMomentRow2007 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3493) := by
    have ha : gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge = raw41420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41420 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2007).leftCharge (GramAssembly.key 2007).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2007, Integer.Sparse.eval]

theorem keyMoment2008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2008) =
      Integer.Sparse.eval keyMomentRow2008 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3805) := by
    have ha : gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge = raw41421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41421 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2008).leftCharge (GramAssembly.key 2008).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2008, Integer.Sparse.eval]

theorem keyMoment2009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2009) =
      Integer.Sparse.eval keyMomentRow2009 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2807) := by
    have ha : gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge = raw41422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41422 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2009).leftCharge (GramAssembly.key 2009).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2009, Integer.Sparse.eval]

theorem keyMoment2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2010) =
      Integer.Sparse.eval keyMomentRow2010 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3703) := by
    have ha : gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge = raw41423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41423 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2010).leftCharge (GramAssembly.key 2010).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2010, Integer.Sparse.eval]

theorem keyMoment2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2011) =
      Integer.Sparse.eval keyMomentRow2011 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3689) := by
    have ha : gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge = raw41424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41424 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2011).leftCharge (GramAssembly.key 2011).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2011, Integer.Sparse.eval]

theorem keyMoment2012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2012) =
      Integer.Sparse.eval keyMomentRow2012 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1964) := by
    have ha : gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge = raw41425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41425 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2012).leftCharge (GramAssembly.key 2012).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2012, Integer.Sparse.eval]

theorem keyMoment2013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2013) =
      Integer.Sparse.eval keyMomentRow2013 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3496) := by
    have ha : gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge = raw41426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41426 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2013).leftCharge (GramAssembly.key 2013).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2013, Integer.Sparse.eval]

theorem keyMoment2014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2014) =
      Integer.Sparse.eval keyMomentRow2014 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1126) := by
    have ha : gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge = raw41427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41427 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2014).leftCharge (GramAssembly.key 2014).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2014, Integer.Sparse.eval]

theorem keyMoment2015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2015) =
      Integer.Sparse.eval keyMomentRow2015 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2508) := by
    have ha : gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge = raw41428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41428 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2015).leftCharge (GramAssembly.key 2015).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2015, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
