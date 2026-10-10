import OAI.Analysis.MutuallyUnbiased.MixedTargets.Keys60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical322
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical323

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1920) =
      Integer.Sparse.eval keyMomentRow1920 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge = raw41333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41333 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1920, Integer.Sparse.eval]

theorem keyMoment1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1921) =
      Integer.Sparse.eval keyMomentRow1921 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3720) := by
    have ha : gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge = raw41334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41334 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1921, Integer.Sparse.eval]

theorem keyMoment1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1922) =
      Integer.Sparse.eval keyMomentRow1922 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge = raw41335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41335 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1922, Integer.Sparse.eval]

theorem keyMoment1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1923) =
      Integer.Sparse.eval keyMomentRow1923 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2925) := by
    have ha : gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge = raw41336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41336 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1923, Integer.Sparse.eval]

theorem keyMoment1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1924) =
      Integer.Sparse.eval keyMomentRow1924 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1237) := by
    have ha : gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge = raw41337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41337 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1924, Integer.Sparse.eval]

theorem keyMoment1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1925) =
      Integer.Sparse.eval keyMomentRow1925 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2575) := by
    have ha : gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge = raw41338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41338 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1925, Integer.Sparse.eval]

theorem keyMoment1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1926) =
      Integer.Sparse.eval keyMomentRow1926 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2545) := by
    have ha : gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge = raw41339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41339 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1926, Integer.Sparse.eval]

theorem keyMoment1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1927) =
      Integer.Sparse.eval keyMomentRow1927 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1215) := by
    have ha : gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge = raw41340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41340 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1927, Integer.Sparse.eval]

theorem keyMoment1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1928) =
      Integer.Sparse.eval keyMomentRow1928 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3906) := by
    have ha : gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge = raw41341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41341 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1928, Integer.Sparse.eval]

theorem keyMoment1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1929) =
      Integer.Sparse.eval keyMomentRow1929 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge = raw41342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41342 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1929, Integer.Sparse.eval]

theorem keyMoment1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1930) =
      Integer.Sparse.eval keyMomentRow1930 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2028) := by
    have ha : gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge = raw41343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41343 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1930, Integer.Sparse.eval]

theorem keyMoment1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1931) =
      Integer.Sparse.eval keyMomentRow1931 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3533) := by
    have ha : gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge = raw41344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41344 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1931, Integer.Sparse.eval]

theorem keyMoment1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1932) =
      Integer.Sparse.eval keyMomentRow1932 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge = raw41345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41345 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1932, Integer.Sparse.eval]

theorem keyMoment1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1933) =
      Integer.Sparse.eval keyMomentRow1933 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge = raw41346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41346 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1933, Integer.Sparse.eval]

theorem keyMoment1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1934) =
      Integer.Sparse.eval keyMomentRow1934 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3719) := by
    have ha : gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge = raw41347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41347 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1934, Integer.Sparse.eval]

theorem keyMoment1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1935) =
      Integer.Sparse.eval keyMomentRow1935 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge = raw41348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41348 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1935, Integer.Sparse.eval]

theorem keyMoment1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1936) =
      Integer.Sparse.eval keyMomentRow1936 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3901) := by
    have ha : gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge = raw41349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41349 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1936, Integer.Sparse.eval]

theorem keyMoment1937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1937) =
      Integer.Sparse.eval keyMomentRow1937 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3837) := by
    have ha : gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge = raw41350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41350 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1937, Integer.Sparse.eval]

theorem keyMoment1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1938) =
      Integer.Sparse.eval keyMomentRow1938 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2025) := by
    have ha : gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge = raw41351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41351 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1938, Integer.Sparse.eval]

theorem keyMoment1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1939) =
      Integer.Sparse.eval keyMomentRow1939 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge = raw41352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41352 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1939, Integer.Sparse.eval]

theorem keyMoment1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1940) =
      Integer.Sparse.eval keyMomentRow1940 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2924) := by
    have ha : gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge = raw41353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41353 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1940, Integer.Sparse.eval]

theorem keyMoment1941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1941) =
      Integer.Sparse.eval keyMomentRow1941 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge = raw41354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41354 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1941, Integer.Sparse.eval]

theorem keyMoment1942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1942) =
      Integer.Sparse.eval keyMomentRow1942 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1236) := by
    have ha : gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge = raw41355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41355 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1942, Integer.Sparse.eval]

theorem keyMoment1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1943) =
      Integer.Sparse.eval keyMomentRow1943 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge = raw41356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41356 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1943, Integer.Sparse.eval]

theorem keyMoment1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1944) =
      Integer.Sparse.eval keyMomentRow1944 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge = raw41357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41357 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1944, Integer.Sparse.eval]

theorem keyMoment1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1945) =
      Integer.Sparse.eval keyMomentRow1945 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1235) := by
    have ha : gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge = raw41358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41358 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1945, Integer.Sparse.eval]

theorem keyMoment1946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1946) =
      Integer.Sparse.eval keyMomentRow1946 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge = raw41359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41359 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1946, Integer.Sparse.eval]

theorem keyMoment1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1947) =
      Integer.Sparse.eval keyMomentRow1947 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge = raw41360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41360 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1947, Integer.Sparse.eval]

theorem keyMoment1948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1948) =
      Integer.Sparse.eval keyMomentRow1948 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge = raw41361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41361 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1948, Integer.Sparse.eval]

theorem keyMoment1949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1949) =
      Integer.Sparse.eval keyMomentRow1949 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3693) := by
    have ha : gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge = raw41362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41362 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1949, Integer.Sparse.eval]

theorem keyMoment1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1950) =
      Integer.Sparse.eval keyMomentRow1950 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge = raw41363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41363 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1950, Integer.Sparse.eval]

theorem keyMoment1951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1951) =
      Integer.Sparse.eval keyMomentRow1951 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3902) := by
    have ha : gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge = raw41364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41364 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1951, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
