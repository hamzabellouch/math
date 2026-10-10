import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment960 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 960) =
      Integer.Sparse.eval keyMomentRow960 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1971) := by
    have ha : gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge = raw40400 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40400Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40400 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 960).leftCharge (GramAssembly.key 960).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow960, Integer.Sparse.eval]

theorem keyMoment961 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 961) =
      Integer.Sparse.eval keyMomentRow961 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2026) := by
    have ha : gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge = raw40401 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40401Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40401 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 961).leftCharge (GramAssembly.key 961).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow961, Integer.Sparse.eval]

theorem keyMoment962 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 962) =
      Integer.Sparse.eval keyMomentRow962 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge = raw40402 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40402Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40402 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 962).leftCharge (GramAssembly.key 962).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow962, Integer.Sparse.eval]

theorem keyMoment963 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 963) =
      Integer.Sparse.eval keyMomentRow963 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1976) := by
    have ha : gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge = raw40403 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40403Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40403 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 963).leftCharge (GramAssembly.key 963).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow963, Integer.Sparse.eval]

theorem keyMoment964 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 964) =
      Integer.Sparse.eval keyMomentRow964 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1793) := by
    have ha : gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge = raw40404 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40404Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40404 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 964).leftCharge (GramAssembly.key 964).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow964, Integer.Sparse.eval]

theorem keyMoment965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 965) =
      Integer.Sparse.eval keyMomentRow965 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1965) := by
    have ha : gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge = raw40405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 965).leftCharge (GramAssembly.key 965).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow965, Integer.Sparse.eval]

theorem keyMoment966 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 966) =
      Integer.Sparse.eval keyMomentRow966 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2010) := by
    have ha : gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge = raw40406 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40406Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40406 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 966).leftCharge (GramAssembly.key 966).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow966, Integer.Sparse.eval]

theorem keyMoment967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 967) =
      Integer.Sparse.eval keyMomentRow967 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1957) := by
    have ha : gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge = raw40407 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40407Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40407 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 967).leftCharge (GramAssembly.key 967).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow967, Integer.Sparse.eval]

theorem keyMoment968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 968) =
      Integer.Sparse.eval keyMomentRow968 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge = raw40408 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40408Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40408 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 968).leftCharge (GramAssembly.key 968).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow968, Integer.Sparse.eval]

theorem keyMoment969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 969) =
      Integer.Sparse.eval keyMomentRow969 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2716) := by
    have ha : gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge = raw40409 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40409Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40409 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 969).leftCharge (GramAssembly.key 969).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow969, Integer.Sparse.eval]

theorem keyMoment970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 970) =
      Integer.Sparse.eval keyMomentRow970 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3033) := by
    have ha : gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge = raw40410 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40410Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40410 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 970).leftCharge (GramAssembly.key 970).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow970, Integer.Sparse.eval]

theorem keyMoment971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 971) =
      Integer.Sparse.eval keyMomentRow971 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3156) := by
    have ha : gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge = raw40411 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40411Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40411 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 971).leftCharge (GramAssembly.key 971).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow971, Integer.Sparse.eval]

theorem keyMoment972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 972) =
      Integer.Sparse.eval keyMomentRow972 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3222) := by
    have ha : gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge = raw40412 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40412Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40412 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 972).leftCharge (GramAssembly.key 972).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow972, Integer.Sparse.eval]

theorem keyMoment973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 973) =
      Integer.Sparse.eval keyMomentRow973 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3180) := by
    have ha : gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge = raw40413 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40413Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40413 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 973).leftCharge (GramAssembly.key 973).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow973, Integer.Sparse.eval]

theorem keyMoment974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 974) =
      Integer.Sparse.eval keyMomentRow974 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3131) := by
    have ha : gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge = raw40414 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40414Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40414 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 974).leftCharge (GramAssembly.key 974).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow974, Integer.Sparse.eval]

theorem keyMoment975 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 975) =
      Integer.Sparse.eval keyMomentRow975 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3062) := by
    have ha : gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge = raw40415 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40415Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40415 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 975).leftCharge (GramAssembly.key 975).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow975, Integer.Sparse.eval]

theorem keyMoment976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 976) =
      Integer.Sparse.eval keyMomentRow976 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3196) := by
    have ha : gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge = raw40416 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40416Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40416 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 976).leftCharge (GramAssembly.key 976).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow976, Integer.Sparse.eval]

theorem keyMoment977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 977) =
      Integer.Sparse.eval keyMomentRow977 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3202) := by
    have ha : gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge = raw40417 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40417Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40417 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 977).leftCharge (GramAssembly.key 977).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow977, Integer.Sparse.eval]

theorem keyMoment978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 978) =
      Integer.Sparse.eval keyMomentRow978 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3163) := by
    have ha : gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge = raw40418 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40418Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40418 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 978).leftCharge (GramAssembly.key 978).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow978, Integer.Sparse.eval]

theorem keyMoment979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 979) =
      Integer.Sparse.eval keyMomentRow979 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3136) := by
    have ha : gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge = raw40419 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40419Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40419 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 979).leftCharge (GramAssembly.key 979).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow979, Integer.Sparse.eval]

theorem keyMoment980 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 980) =
      Integer.Sparse.eval keyMomentRow980 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3134) := by
    have ha : gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge = raw40420 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40420Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40420 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 980).leftCharge (GramAssembly.key 980).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow980, Integer.Sparse.eval]

theorem keyMoment981 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 981) =
      Integer.Sparse.eval keyMomentRow981 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3127) := by
    have ha : gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge = raw40421 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40421Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40421 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 981).leftCharge (GramAssembly.key 981).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow981, Integer.Sparse.eval]

theorem keyMoment982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 982) =
      Integer.Sparse.eval keyMomentRow982 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3170) := by
    have ha : gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge = raw40422 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40422Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40422 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 982).leftCharge (GramAssembly.key 982).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow982, Integer.Sparse.eval]

theorem keyMoment983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 983) =
      Integer.Sparse.eval keyMomentRow983 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge = raw40423 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40423Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40423 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 983).leftCharge (GramAssembly.key 983).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow983, Integer.Sparse.eval]

theorem keyMoment984 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 984) =
      Integer.Sparse.eval keyMomentRow984 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3161) := by
    have ha : gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge = raw40424 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40424Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40424 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 984).leftCharge (GramAssembly.key 984).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow984, Integer.Sparse.eval]

theorem keyMoment985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 985) =
      Integer.Sparse.eval keyMomentRow985 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2821) := by
    have ha : gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge = raw40425 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40425Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40425 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 985).leftCharge (GramAssembly.key 985).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow985, Integer.Sparse.eval]

theorem keyMoment986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 986) =
      Integer.Sparse.eval keyMomentRow986 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3198) := by
    have ha : gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge = raw40426 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40426Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40426 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 986).leftCharge (GramAssembly.key 986).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow986, Integer.Sparse.eval]

theorem keyMoment987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 987) =
      Integer.Sparse.eval keyMomentRow987 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2816) := by
    have ha : gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge = raw40427 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40427Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40427 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 987).leftCharge (GramAssembly.key 987).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow987, Integer.Sparse.eval]

theorem keyMoment988 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 988) =
      Integer.Sparse.eval keyMomentRow988 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3138) := by
    have ha : gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge = raw40428 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40428Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40428 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 988).leftCharge (GramAssembly.key 988).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow988, Integer.Sparse.eval]

theorem keyMoment989 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 989) =
      Integer.Sparse.eval keyMomentRow989 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2803) := by
    have ha : gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge = raw40429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40429 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 989).leftCharge (GramAssembly.key 989).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow989, Integer.Sparse.eval]

theorem keyMoment990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 990) =
      Integer.Sparse.eval keyMomentRow990 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3129) := by
    have ha : gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge = raw40430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40430 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 990).leftCharge (GramAssembly.key 990).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow990, Integer.Sparse.eval]

theorem keyMoment991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 991) =
      Integer.Sparse.eval keyMomentRow991 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3174) := by
    have ha : gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge = raw40431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40431 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 991).leftCharge (GramAssembly.key 991).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow991, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
