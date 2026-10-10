import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical323

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1952) =
      Integer.Sparse.eval keyMomentRow1952 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3721) := by
    have ha : gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge = raw41365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41365 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1952).leftCharge (GramAssembly.key 1952).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1952, Integer.Sparse.eval]

theorem keyMoment1953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1953) =
      Integer.Sparse.eval keyMomentRow1953 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3838) := by
    have ha : gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge = raw41366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41366 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1953).leftCharge (GramAssembly.key 1953).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1953, Integer.Sparse.eval]

theorem keyMoment1954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1954) =
      Integer.Sparse.eval keyMomentRow1954 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3689) := by
    have ha : gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge = raw41367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41367 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1954).leftCharge (GramAssembly.key 1954).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1954, Integer.Sparse.eval]

theorem keyMoment1955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1955) =
      Integer.Sparse.eval keyMomentRow1955 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge = raw41368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41368 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1955).leftCharge (GramAssembly.key 1955).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1955, Integer.Sparse.eval]

theorem keyMoment1956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1956) =
      Integer.Sparse.eval keyMomentRow1956 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3692) := by
    have ha : gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge = raw41369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41369 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1956).leftCharge (GramAssembly.key 1956).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1956, Integer.Sparse.eval]

theorem keyMoment1957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1957) =
      Integer.Sparse.eval keyMomentRow1957 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2931) := by
    have ha : gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge = raw41370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41370 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1957).leftCharge (GramAssembly.key 1957).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1957, Integer.Sparse.eval]

theorem keyMoment1958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1958) =
      Integer.Sparse.eval keyMomentRow1958 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge = raw41371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41371 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1958).leftCharge (GramAssembly.key 1958).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1958, Integer.Sparse.eval]

theorem keyMoment1959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1959) =
      Integer.Sparse.eval keyMomentRow1959 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1246) := by
    have ha : gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge = raw41372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41372 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1959).leftCharge (GramAssembly.key 1959).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1959, Integer.Sparse.eval]

theorem keyMoment1960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1960) =
      Integer.Sparse.eval keyMomentRow1960 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge = raw41373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41373 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1960).leftCharge (GramAssembly.key 1960).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1960, Integer.Sparse.eval]

theorem keyMoment1961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1961) =
      Integer.Sparse.eval keyMomentRow1961 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1240) := by
    have ha : gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge = raw41374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41374 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1961).leftCharge (GramAssembly.key 1961).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1961, Integer.Sparse.eval]

theorem keyMoment1962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1962) =
      Integer.Sparse.eval keyMomentRow1962 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2723) := by
    have ha : gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge = raw41375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41375 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1962).leftCharge (GramAssembly.key 1962).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1962, Integer.Sparse.eval]

theorem keyMoment1963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1963) =
      Integer.Sparse.eval keyMomentRow1963 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2561) := by
    have ha : gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge = raw41376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41376 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1963).leftCharge (GramAssembly.key 1963).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1963, Integer.Sparse.eval]

theorem keyMoment1964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1964) =
      Integer.Sparse.eval keyMomentRow1964 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2556) := by
    have ha : gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge = raw41377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41377 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1964).leftCharge (GramAssembly.key 1964).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1964, Integer.Sparse.eval]

theorem keyMoment1965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1965) =
      Integer.Sparse.eval keyMomentRow1965 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge = raw41378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41378 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1965).leftCharge (GramAssembly.key 1965).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1965, Integer.Sparse.eval]

theorem keyMoment1966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1966) =
      Integer.Sparse.eval keyMomentRow1966 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2488) := by
    have ha : gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge = raw41379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41379 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1966).leftCharge (GramAssembly.key 1966).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1966, Integer.Sparse.eval]

theorem keyMoment1967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1967) =
      Integer.Sparse.eval keyMomentRow1967 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge = raw41380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41380 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1967).leftCharge (GramAssembly.key 1967).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1967, Integer.Sparse.eval]

theorem keyMoment1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1968) =
      Integer.Sparse.eval keyMomentRow1968 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2479) := by
    have ha : gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge = raw41381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41381 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1968).leftCharge (GramAssembly.key 1968).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1968, Integer.Sparse.eval]

theorem keyMoment1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1969) =
      Integer.Sparse.eval keyMomentRow1969 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge = raw41382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41382 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1969).leftCharge (GramAssembly.key 1969).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1969, Integer.Sparse.eval]

theorem keyMoment1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1970) =
      Integer.Sparse.eval keyMomentRow1970 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2483) := by
    have ha : gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge = raw41383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41383 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1970).leftCharge (GramAssembly.key 1970).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1970, Integer.Sparse.eval]

theorem keyMoment1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1971) =
      Integer.Sparse.eval keyMomentRow1971 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1242) := by
    have ha : gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge = raw41384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41384 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1971).leftCharge (GramAssembly.key 1971).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1971, Integer.Sparse.eval]

theorem keyMoment1972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1972) =
      Integer.Sparse.eval keyMomentRow1972 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2726) := by
    have ha : gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge = raw41385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41385 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1972).leftCharge (GramAssembly.key 1972).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1972, Integer.Sparse.eval]

theorem keyMoment1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1973) =
      Integer.Sparse.eval keyMomentRow1973 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2482) := by
    have ha : gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge = raw41386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41386 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1973).leftCharge (GramAssembly.key 1973).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1973, Integer.Sparse.eval]

theorem keyMoment1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1974) =
      Integer.Sparse.eval keyMomentRow1974 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1049) := by
    have ha : gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge = raw41387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41387 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1974).leftCharge (GramAssembly.key 1974).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1974, Integer.Sparse.eval]

theorem keyMoment1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1975) =
      Integer.Sparse.eval keyMomentRow1975 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1044) := by
    have ha : gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge = raw41388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41388 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1975).leftCharge (GramAssembly.key 1975).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1975, Integer.Sparse.eval]

theorem keyMoment1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1976) =
      Integer.Sparse.eval keyMomentRow1976 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1046) := by
    have ha : gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge = raw41389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41389 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1976).leftCharge (GramAssembly.key 1976).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1976, Integer.Sparse.eval]

theorem keyMoment1977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1977) =
      Integer.Sparse.eval keyMomentRow1977 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1051) := by
    have ha : gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge = raw41390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41390 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1977).leftCharge (GramAssembly.key 1977).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1977, Integer.Sparse.eval]

theorem keyMoment1978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1978) =
      Integer.Sparse.eval keyMomentRow1978 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2131) := by
    have ha : gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge = raw41391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41391 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1978).leftCharge (GramAssembly.key 1978).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1978, Integer.Sparse.eval]

theorem keyMoment1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1979) =
      Integer.Sparse.eval keyMomentRow1979 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1821) := by
    have ha : gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge = raw41392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41392 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1979).leftCharge (GramAssembly.key 1979).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1979, Integer.Sparse.eval]

theorem keyMoment1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1980) =
      Integer.Sparse.eval keyMomentRow1980 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge = raw41393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41393 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1980).leftCharge (GramAssembly.key 1980).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1980, Integer.Sparse.eval]

theorem keyMoment1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1981) =
      Integer.Sparse.eval keyMomentRow1981 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2104) := by
    have ha : gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge = raw41394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41394 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1981).leftCharge (GramAssembly.key 1981).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1981, Integer.Sparse.eval]

theorem keyMoment1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1982) =
      Integer.Sparse.eval keyMomentRow1982 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge = raw41395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41395 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1982).leftCharge (GramAssembly.key 1982).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1982, Integer.Sparse.eval]

theorem keyMoment1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1983) =
      Integer.Sparse.eval keyMomentRow1983 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2806) := by
    have ha : gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge = raw41396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41396 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1983).leftCharge (GramAssembly.key 1983).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1983, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
