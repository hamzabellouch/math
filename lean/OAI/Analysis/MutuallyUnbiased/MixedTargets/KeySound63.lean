import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical323

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2016) =
      Integer.Sparse.eval keyMomentRow2016 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2479) := by
    have ha : gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge = raw41429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41429 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2016, Integer.Sparse.eval]

theorem keyMoment2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2017) =
      Integer.Sparse.eval keyMomentRow2017 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 599) := by
    have ha : gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge = raw41430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41430 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2017, Integer.Sparse.eval]

theorem keyMoment2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2018) =
      Integer.Sparse.eval keyMomentRow2018 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1039) := by
    have ha : gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge = raw41431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41431 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2018, Integer.Sparse.eval]

theorem keyMoment2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2019) =
      Integer.Sparse.eval keyMomentRow2019 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1827) := by
    have ha : gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge = raw41432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41432 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2019, Integer.Sparse.eval]

theorem keyMoment2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2020) =
      Integer.Sparse.eval keyMomentRow2020 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1792) := by
    have ha : gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge = raw41433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2020, Integer.Sparse.eval]

theorem keyMoment2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2021) =
      Integer.Sparse.eval keyMomentRow2021 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 583) := by
    have ha : gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge = raw41434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41434 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2021, Integer.Sparse.eval]

theorem keyMoment2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2022) =
      Integer.Sparse.eval keyMomentRow2022 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge = raw41435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41435 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2022, Integer.Sparse.eval]

theorem keyMoment2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2023) =
      Integer.Sparse.eval keyMomentRow2023 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2107) := by
    have ha : gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge = raw41436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41436 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2023, Integer.Sparse.eval]

theorem keyMoment2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2024) =
      Integer.Sparse.eval keyMomentRow2024 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1810) := by
    have ha : gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge = raw41437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41437 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2024, Integer.Sparse.eval]

theorem keyMoment2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2025) =
      Integer.Sparse.eval keyMomentRow2025 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2054) := by
    have ha : gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge = raw41438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41438 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2025, Integer.Sparse.eval]

theorem keyMoment2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2026) =
      Integer.Sparse.eval keyMomentRow2026 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge = raw41439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2026, Integer.Sparse.eval]

theorem keyMoment2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2027) =
      Integer.Sparse.eval keyMomentRow2027 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1805) := by
    have ha : gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge = raw41440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41440 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2027, Integer.Sparse.eval]

theorem keyMoment2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2028) =
      Integer.Sparse.eval keyMomentRow2028 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2020) := by
    have ha : gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge = raw41441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41441 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2028, Integer.Sparse.eval]

theorem keyMoment2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2029) =
      Integer.Sparse.eval keyMomentRow2029 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge = raw41442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41442 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2029, Integer.Sparse.eval]

theorem keyMoment2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2030) =
      Integer.Sparse.eval keyMomentRow2030 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3787) := by
    have ha : gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge = raw41443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41443 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2030, Integer.Sparse.eval]

theorem keyMoment2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2031) =
      Integer.Sparse.eval keyMomentRow2031 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3671) := by
    have ha : gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge = raw41444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41444 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2031, Integer.Sparse.eval]

theorem keyMoment2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2032) =
      Integer.Sparse.eval keyMomentRow2032 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3781) := by
    have ha : gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge = raw41445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41445 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2032, Integer.Sparse.eval]

theorem keyMoment2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2033) =
      Integer.Sparse.eval keyMomentRow2033 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge = raw41446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41446 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2033, Integer.Sparse.eval]

theorem keyMoment2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2034) =
      Integer.Sparse.eval keyMomentRow2034 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2813) := by
    have ha : gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge = raw41447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41447 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2034, Integer.Sparse.eval]

theorem keyMoment2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2035) =
      Integer.Sparse.eval keyMomentRow2035 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3705) := by
    have ha : gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge = raw41448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41448 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2035, Integer.Sparse.eval]

theorem keyMoment2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2036) =
      Integer.Sparse.eval keyMomentRow2036 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2809) := by
    have ha : gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge = raw41449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41449 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2036, Integer.Sparse.eval]

theorem keyMoment2037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2037) =
      Integer.Sparse.eval keyMomentRow2037 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3690) := by
    have ha : gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge = raw41450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2037, Integer.Sparse.eval]

theorem keyMoment2038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2038) =
      Integer.Sparse.eval keyMomentRow2038 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3670) := by
    have ha : gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge = raw41451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2038, Integer.Sparse.eval]

theorem keyMoment2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2039) =
      Integer.Sparse.eval keyMomentRow2039 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3909) := by
    have ha : gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge = raw41452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2039, Integer.Sparse.eval]

theorem keyMoment2040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2040) =
      Integer.Sparse.eval keyMomentRow2040 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2893) := by
    have ha : gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge = raw41453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2040, Integer.Sparse.eval]

theorem keyMoment2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2041) =
      Integer.Sparse.eval keyMomentRow2041 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3945) := by
    have ha : gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge = raw41454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2041, Integer.Sparse.eval]

theorem keyMoment2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2042) =
      Integer.Sparse.eval keyMomentRow2042 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1134) := by
    have ha : gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge = raw41455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2042, Integer.Sparse.eval]

theorem keyMoment2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2043) =
      Integer.Sparse.eval keyMomentRow2043 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2512) := by
    have ha : gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge = raw41456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2043, Integer.Sparse.eval]

theorem keyMoment2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2044) =
      Integer.Sparse.eval keyMomentRow2044 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1129) := by
    have ha : gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge = raw41457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2044, Integer.Sparse.eval]

theorem keyMoment2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2045) =
      Integer.Sparse.eval keyMomentRow2045 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2480) := by
    have ha : gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge = raw41458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2045, Integer.Sparse.eval]

theorem keyMoment2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2046) =
      Integer.Sparse.eval keyMomentRow2046 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2428) := by
    have ha : gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge = raw41459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2046, Integer.Sparse.eval]

theorem keyMoment2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2047) =
      Integer.Sparse.eval keyMomentRow2047 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 608) := by
    have ha : gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge = raw41460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2047, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
