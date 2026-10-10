import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical315

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 928) =
      Integer.Sparse.eval keyMomentRow928 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2964) := by
    have ha : gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge = raw40368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40368 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow928, Integer.Sparse.eval]

theorem keyMoment929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 929) =
      Integer.Sparse.eval keyMomentRow929 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3096) := by
    have ha : gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge = raw40369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40369 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow929, Integer.Sparse.eval]

theorem keyMoment930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 930) =
      Integer.Sparse.eval keyMomentRow930 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge = raw40370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40370 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow930, Integer.Sparse.eval]

theorem keyMoment931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 931) =
      Integer.Sparse.eval keyMomentRow931 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3084) := by
    have ha : gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge = raw40371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40371 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow931, Integer.Sparse.eval]

theorem keyMoment932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 932) =
      Integer.Sparse.eval keyMomentRow932 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge = raw40372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40372 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow932, Integer.Sparse.eval]

theorem keyMoment933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 933) =
      Integer.Sparse.eval keyMomentRow933 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1310) := by
    have ha : gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge = raw40373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40373 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow933, Integer.Sparse.eval]

theorem keyMoment934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 934) =
      Integer.Sparse.eval keyMomentRow934 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge = raw40374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40374 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow934, Integer.Sparse.eval]

theorem keyMoment935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 935) =
      Integer.Sparse.eval keyMomentRow935 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1306) := by
    have ha : gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge = raw40375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40375 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow935, Integer.Sparse.eval]

theorem keyMoment936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 936) =
      Integer.Sparse.eval keyMomentRow936 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2643) := by
    have ha : gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge = raw40376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40376 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow936, Integer.Sparse.eval]

theorem keyMoment937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 937) =
      Integer.Sparse.eval keyMomentRow937 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1273) := by
    have ha : gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge = raw40377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40377 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow937, Integer.Sparse.eval]

theorem keyMoment938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 938) =
      Integer.Sparse.eval keyMomentRow938 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2603) := by
    have ha : gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge = raw40378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40378 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow938, Integer.Sparse.eval]

theorem keyMoment939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 939) =
      Integer.Sparse.eval keyMomentRow939 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge = raw40379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40379 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow939, Integer.Sparse.eval]

theorem keyMoment940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 940) =
      Integer.Sparse.eval keyMomentRow940 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3118) := by
    have ha : gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge = raw40380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40380 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow940, Integer.Sparse.eval]

theorem keyMoment941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 941) =
      Integer.Sparse.eval keyMomentRow941 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2641) := by
    have ha : gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge = raw40381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40381 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow941, Integer.Sparse.eval]

theorem keyMoment942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 942) =
      Integer.Sparse.eval keyMomentRow942 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1270) := by
    have ha : gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge = raw40382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40382 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow942, Integer.Sparse.eval]

theorem keyMoment943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 943) =
      Integer.Sparse.eval keyMomentRow943 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2600) := by
    have ha : gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge = raw40383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40383 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow943, Integer.Sparse.eval]

theorem keyMoment944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 944) =
      Integer.Sparse.eval keyMomentRow944 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge = raw40384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40384 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow944, Integer.Sparse.eval]

theorem keyMoment945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 945) =
      Integer.Sparse.eval keyMomentRow945 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3108) := by
    have ha : gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge = raw40385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40385 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow945, Integer.Sparse.eval]

theorem keyMoment946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 946) =
      Integer.Sparse.eval keyMomentRow946 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2575) := by
    have ha : gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge = raw40386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40386 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow946, Integer.Sparse.eval]

theorem keyMoment947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 947) =
      Integer.Sparse.eval keyMomentRow947 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2573) := by
    have ha : gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge = raw40387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40387 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow947, Integer.Sparse.eval]

theorem keyMoment948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 948) =
      Integer.Sparse.eval keyMomentRow948 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2285) := by
    have ha : gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge = raw40388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40388 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow948, Integer.Sparse.eval]

theorem keyMoment949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 949) =
      Integer.Sparse.eval keyMomentRow949 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2136) := by
    have ha : gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge = raw40389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40389 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow949, Integer.Sparse.eval]

theorem keyMoment950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 950) =
      Integer.Sparse.eval keyMomentRow950 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1832) := by
    have ha : gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge = raw40390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40390 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow950, Integer.Sparse.eval]

theorem keyMoment951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 951) =
      Integer.Sparse.eval keyMomentRow951 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge = raw40391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40391 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow951, Integer.Sparse.eval]

theorem keyMoment952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 952) =
      Integer.Sparse.eval keyMomentRow952 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2113) := by
    have ha : gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge = raw40392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40392 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow952, Integer.Sparse.eval]

theorem keyMoment953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 953) =
      Integer.Sparse.eval keyMomentRow953 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1820) := by
    have ha : gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge = raw40393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40393 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow953, Integer.Sparse.eval]

theorem keyMoment954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 954) =
      Integer.Sparse.eval keyMomentRow954 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1828) := by
    have ha : gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge = raw40394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40394 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow954, Integer.Sparse.eval]

theorem keyMoment955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 955) =
      Integer.Sparse.eval keyMomentRow955 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2037) := by
    have ha : gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge = raw40395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40395 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow955, Integer.Sparse.eval]

theorem keyMoment956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 956) =
      Integer.Sparse.eval keyMomentRow956 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2092) := by
    have ha : gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge = raw40396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40396 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow956, Integer.Sparse.eval]

theorem keyMoment957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 957) =
      Integer.Sparse.eval keyMomentRow957 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1813) := by
    have ha : gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge = raw40397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40397 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow957, Integer.Sparse.eval]

theorem keyMoment958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 958) =
      Integer.Sparse.eval keyMomentRow958 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1980) := by
    have ha : gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge = raw40398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40398 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow958, Integer.Sparse.eval]

theorem keyMoment959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 959) =
      Integer.Sparse.eval keyMomentRow959 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1797) := by
    have ha : gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge = raw40399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40399 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow959, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
