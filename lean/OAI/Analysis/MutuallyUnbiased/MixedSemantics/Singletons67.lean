import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4288 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4288 node4288Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node866 node866Labels + mixedMoment B node1554 node1554Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1026 singletonSmall4288
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4288) = raw1026Labels := by decide +kernel
  rw [hl, canonical1026 B hB] at h
  have hc0 : mixedMoment B raw1026 (Fin.cases (0 : Fin 2) singletonSmall4288) =
      mixedMoment B node866 node866Labels := by
    have ha : raw1026 = raw1027 := by apply Matrix.ext; unfold raw1026 raw1027; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4288 = raw1027Labels := by decide +kernel
    rw [ha, hj, canonical1027 B hB]
  have hc1 : mixedMoment B raw1026 (Fin.cases (1 : Fin 2) singletonSmall4288) =
      mixedMoment B node1554 node1554Labels := by
    have ha : raw1026 = raw1028 := by apply Matrix.ext; unfold raw1026 raw1028; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4288 = raw1028Labels := by decide +kernel
    rw [ha, hj, canonical1028 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4289 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4289 node4289Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node867 node867Labels + mixedMoment B node1555 node1555Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1029 singletonSmall4289
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4289) = raw1029Labels := by decide +kernel
  rw [hl, canonical1029 B hB] at h
  have hc0 : mixedMoment B raw1029 (Fin.cases (0 : Fin 2) singletonSmall4289) =
      mixedMoment B node867 node867Labels := by
    have ha : raw1029 = raw1030 := by apply Matrix.ext; unfold raw1029 raw1030; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4289 = raw1030Labels := by decide +kernel
    rw [ha, hj, canonical1030 B hB]
  have hc1 : mixedMoment B raw1029 (Fin.cases (1 : Fin 2) singletonSmall4289) =
      mixedMoment B node1555 node1555Labels := by
    have ha : raw1029 = raw1031 := by apply Matrix.ext; unfold raw1029 raw1031; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4289 = raw1031Labels := by decide +kernel
    rw [ha, hj, canonical1031 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4290 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4290 node4290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node868 node868Labels + mixedMoment B node1566 node1566Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1032 singletonSmall4290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4290) = raw1032Labels := by decide +kernel
  rw [hl, canonical1032 B hB] at h
  have hc0 : mixedMoment B raw1032 (Fin.cases (0 : Fin 2) singletonSmall4290) =
      mixedMoment B node868 node868Labels := by
    have ha : raw1032 = raw1033 := by apply Matrix.ext; unfold raw1032 raw1033; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4290 = raw1033Labels := by decide +kernel
    rw [ha, hj, canonical1033 B hB]
  have hc1 : mixedMoment B raw1032 (Fin.cases (1 : Fin 2) singletonSmall4290) =
      mixedMoment B node1566 node1566Labels := by
    have ha : raw1032 = raw1034 := by apply Matrix.ext; unfold raw1032 raw1034; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4290 = raw1034Labels := by decide +kernel
    rw [ha, hj, canonical1034 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4291 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4291 node4291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node869 node869Labels + mixedMoment B node1561 node1561Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1035 singletonSmall4291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4291) = raw1035Labels := by decide +kernel
  rw [hl, canonical1035 B hB] at h
  have hc0 : mixedMoment B raw1035 (Fin.cases (0 : Fin 2) singletonSmall4291) =
      mixedMoment B node869 node869Labels := by
    have ha : raw1035 = raw1036 := by apply Matrix.ext; unfold raw1035 raw1036; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4291 = raw1036Labels := by decide +kernel
    rw [ha, hj, canonical1036 B hB]
  have hc1 : mixedMoment B raw1035 (Fin.cases (1 : Fin 2) singletonSmall4291) =
      mixedMoment B node1561 node1561Labels := by
    have ha : raw1035 = raw1037 := by apply Matrix.ext; unfold raw1035 raw1037; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4291 = raw1037Labels := by decide +kernel
    rw [ha, hj, canonical1037 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4292 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4292 node4292Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node870 node870Labels + mixedMoment B node1567 node1567Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1038 singletonSmall4292
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4292) = raw1038Labels := by decide +kernel
  rw [hl, canonical1038 B hB] at h
  have hc0 : mixedMoment B raw1038 (Fin.cases (0 : Fin 2) singletonSmall4292) =
      mixedMoment B node870 node870Labels := by
    have ha : raw1038 = raw1039 := by apply Matrix.ext; unfold raw1038 raw1039; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4292 = raw1039Labels := by decide +kernel
    rw [ha, hj, canonical1039 B hB]
  have hc1 : mixedMoment B raw1038 (Fin.cases (1 : Fin 2) singletonSmall4292) =
      mixedMoment B node1567 node1567Labels := by
    have ha : raw1038 = raw1040 := by apply Matrix.ext; unfold raw1038 raw1040; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4292 = raw1040Labels := by decide +kernel
    rw [ha, hj, canonical1040 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4293 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4293 node4293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node871 node871Labels + mixedMoment B node1568 node1568Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1041 singletonSmall4293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4293) = raw1041Labels := by decide +kernel
  rw [hl, canonical1041 B hB] at h
  have hc0 : mixedMoment B raw1041 (Fin.cases (0 : Fin 2) singletonSmall4293) =
      mixedMoment B node871 node871Labels := by
    have ha : raw1041 = raw1042 := by apply Matrix.ext; unfold raw1041 raw1042; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4293 = raw1042Labels := by decide +kernel
    rw [ha, hj, canonical1042 B hB]
  have hc1 : mixedMoment B raw1041 (Fin.cases (1 : Fin 2) singletonSmall4293) =
      mixedMoment B node1568 node1568Labels := by
    have ha : raw1041 = raw1043 := by apply Matrix.ext; unfold raw1041 raw1043; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4293 = raw1043Labels := by decide +kernel
    rw [ha, hj, canonical1043 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4294 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4294 node4294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node872 node872Labels + mixedMoment B node1562 node1562Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1044 singletonSmall4294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4294) = raw1044Labels := by decide +kernel
  rw [hl, canonical1044 B hB] at h
  have hc0 : mixedMoment B raw1044 (Fin.cases (0 : Fin 2) singletonSmall4294) =
      mixedMoment B node872 node872Labels := by
    have ha : raw1044 = raw1045 := by apply Matrix.ext; unfold raw1044 raw1045; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4294 = raw1045Labels := by decide +kernel
    rw [ha, hj, canonical1045 B hB]
  have hc1 : mixedMoment B raw1044 (Fin.cases (1 : Fin 2) singletonSmall4294) =
      mixedMoment B node1562 node1562Labels := by
    have ha : raw1044 = raw1046 := by apply Matrix.ext; unfold raw1044 raw1046; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4294 = raw1046Labels := by decide +kernel
    rw [ha, hj, canonical1046 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4295 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4295 node4295Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node873 node873Labels + mixedMoment B node1569 node1569Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1047 singletonSmall4295
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4295) = raw1047Labels := by decide +kernel
  rw [hl, canonical1047 B hB] at h
  have hc0 : mixedMoment B raw1047 (Fin.cases (0 : Fin 2) singletonSmall4295) =
      mixedMoment B node873 node873Labels := by
    have ha : raw1047 = raw1048 := by apply Matrix.ext; unfold raw1047 raw1048; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4295 = raw1048Labels := by decide +kernel
    rw [ha, hj, canonical1048 B hB]
  have hc1 : mixedMoment B raw1047 (Fin.cases (1 : Fin 2) singletonSmall4295) =
      mixedMoment B node1569 node1569Labels := by
    have ha : raw1047 = raw1049 := by apply Matrix.ext; unfold raw1047 raw1049; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4295 = raw1049Labels := by decide +kernel
    rw [ha, hj, canonical1049 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4296 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4296 node4296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node874 node874Labels + mixedMoment B node1570 node1570Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1050 singletonSmall4296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4296) = raw1050Labels := by decide +kernel
  rw [hl, canonical1050 B hB] at h
  have hc0 : mixedMoment B raw1050 (Fin.cases (0 : Fin 2) singletonSmall4296) =
      mixedMoment B node874 node874Labels := by
    have ha : raw1050 = raw1051 := by apply Matrix.ext; unfold raw1050 raw1051; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4296 = raw1051Labels := by decide +kernel
    rw [ha, hj, canonical1051 B hB]
  have hc1 : mixedMoment B raw1050 (Fin.cases (1 : Fin 2) singletonSmall4296) =
      mixedMoment B node1570 node1570Labels := by
    have ha : raw1050 = raw1052 := by apply Matrix.ext; unfold raw1050 raw1052; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4296 = raw1052Labels := by decide +kernel
    rw [ha, hj, canonical1052 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4297 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4297 node4297Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node875 node875Labels + mixedMoment B node1551 node1551Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1053 singletonSmall4297
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4297) = raw1053Labels := by decide +kernel
  rw [hl, canonical1053 B hB] at h
  have hc0 : mixedMoment B raw1053 (Fin.cases (0 : Fin 2) singletonSmall4297) =
      mixedMoment B node875 node875Labels := by
    have ha : raw1053 = raw1054 := by apply Matrix.ext; unfold raw1053 raw1054; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4297 = raw1054Labels := by decide +kernel
    rw [ha, hj, canonical1054 B hB]
  have hc1 : mixedMoment B raw1053 (Fin.cases (1 : Fin 2) singletonSmall4297) =
      mixedMoment B node1551 node1551Labels := by
    have ha : raw1053 = raw1055 := by apply Matrix.ext; unfold raw1053 raw1055; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4297 = raw1055Labels := by decide +kernel
    rw [ha, hj, canonical1055 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4298 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4298 node4298Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node876 node876Labels + mixedMoment B node1552 node1552Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1056 singletonSmall4298
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4298) = raw1056Labels := by decide +kernel
  rw [hl, canonical1056 B hB] at h
  have hc0 : mixedMoment B raw1056 (Fin.cases (0 : Fin 2) singletonSmall4298) =
      mixedMoment B node876 node876Labels := by
    have ha : raw1056 = raw1057 := by apply Matrix.ext; unfold raw1056 raw1057; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4298 = raw1057Labels := by decide +kernel
    rw [ha, hj, canonical1057 B hB]
  have hc1 : mixedMoment B raw1056 (Fin.cases (1 : Fin 2) singletonSmall4298) =
      mixedMoment B node1552 node1552Labels := by
    have ha : raw1056 = raw1058 := by apply Matrix.ext; unfold raw1056 raw1058; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4298 = raw1058Labels := by decide +kernel
    rw [ha, hj, canonical1058 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4299 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4299 node4299Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node877 node877Labels + mixedMoment B node968 node968Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1059 singletonSmall4299
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4299) = raw1059Labels := by decide +kernel
  rw [hl, canonical1059 B hB] at h
  have hc0 : mixedMoment B raw1059 (Fin.cases (0 : Fin 2) singletonSmall4299) =
      mixedMoment B node877 node877Labels := by
    have ha : raw1059 = raw1060 := by apply Matrix.ext; unfold raw1059 raw1060; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4299 = raw1060Labels := by decide +kernel
    rw [ha, hj, canonical1060 B hB]
  have hc1 : mixedMoment B raw1059 (Fin.cases (1 : Fin 2) singletonSmall4299) =
      mixedMoment B node968 node968Labels := by
    have ha : raw1059 = raw1061 := by apply Matrix.ext; unfold raw1059 raw1061; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4299 = raw1061Labels := by decide +kernel
    rw [ha, hj, canonical1061 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4301 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4301 node4301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node879 node879Labels + mixedMoment B node1556 node1556Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1062 singletonSmall4301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4301) = raw1062Labels := by decide +kernel
  rw [hl, canonical1062 B hB] at h
  have hc0 : mixedMoment B raw1062 (Fin.cases (0 : Fin 2) singletonSmall4301) =
      mixedMoment B node879 node879Labels := by
    have ha : raw1062 = raw1063 := by apply Matrix.ext; unfold raw1062 raw1063; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4301 = raw1063Labels := by decide +kernel
    rw [ha, hj, canonical1063 B hB]
  have hc1 : mixedMoment B raw1062 (Fin.cases (1 : Fin 2) singletonSmall4301) =
      mixedMoment B node1556 node1556Labels := by
    have ha : raw1062 = raw1064 := by apply Matrix.ext; unfold raw1062 raw1064; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4301 = raw1064Labels := by decide +kernel
    rw [ha, hj, canonical1064 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4303 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4303 node4303Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node881 node881Labels + mixedMoment B node1559 node1559Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1065 singletonSmall4303
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4303) = raw1065Labels := by decide +kernel
  rw [hl, canonical1065 B hB] at h
  have hc0 : mixedMoment B raw1065 (Fin.cases (0 : Fin 2) singletonSmall4303) =
      mixedMoment B node881 node881Labels := by
    have ha : raw1065 = raw1066 := by apply Matrix.ext; unfold raw1065 raw1066; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4303 = raw1066Labels := by decide +kernel
    rw [ha, hj, canonical1066 B hB]
  have hc1 : mixedMoment B raw1065 (Fin.cases (1 : Fin 2) singletonSmall4303) =
      mixedMoment B node1559 node1559Labels := by
    have ha : raw1065 = raw1067 := by apply Matrix.ext; unfold raw1065 raw1067; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4303 = raw1067Labels := by decide +kernel
    rw [ha, hj, canonical1067 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4304 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4304 node4304Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node882 node882Labels + mixedMoment B node1558 node1558Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1068 singletonSmall4304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4304) = raw1068Labels := by decide +kernel
  rw [hl, canonical1068 B hB] at h
  have hc0 : mixedMoment B raw1068 (Fin.cases (0 : Fin 2) singletonSmall4304) =
      mixedMoment B node882 node882Labels := by
    have ha : raw1068 = raw1069 := by apply Matrix.ext; unfold raw1068 raw1069; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4304 = raw1069Labels := by decide +kernel
    rw [ha, hj, canonical1069 B hB]
  have hc1 : mixedMoment B raw1068 (Fin.cases (1 : Fin 2) singletonSmall4304) =
      mixedMoment B node1558 node1558Labels := by
    have ha : raw1068 = raw1070 := by apply Matrix.ext; unfold raw1068 raw1070; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4304 = raw1070Labels := by decide +kernel
    rw [ha, hj, canonical1070 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4307 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4307 node4307Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node885 node885Labels + mixedMoment B node1563 node1563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1071 singletonSmall4307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4307) = raw1071Labels := by decide +kernel
  rw [hl, canonical1071 B hB] at h
  have hc0 : mixedMoment B raw1071 (Fin.cases (0 : Fin 2) singletonSmall4307) =
      mixedMoment B node885 node885Labels := by
    have ha : raw1071 = raw1072 := by apply Matrix.ext; unfold raw1071 raw1072; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4307 = raw1072Labels := by decide +kernel
    rw [ha, hj, canonical1072 B hB]
  have hc1 : mixedMoment B raw1071 (Fin.cases (1 : Fin 2) singletonSmall4307) =
      mixedMoment B node1563 node1563Labels := by
    have ha : raw1071 = raw1073 := by apply Matrix.ext; unfold raw1071 raw1073; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4307 = raw1073Labels := by decide +kernel
    rw [ha, hj, canonical1073 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4309 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4309 node4309Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node887 node887Labels + mixedMoment B node1573 node1573Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1074 singletonSmall4309
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4309) = raw1074Labels := by decide +kernel
  rw [hl, canonical1074 B hB] at h
  have hc0 : mixedMoment B raw1074 (Fin.cases (0 : Fin 2) singletonSmall4309) =
      mixedMoment B node887 node887Labels := by
    have ha : raw1074 = raw1075 := by apply Matrix.ext; unfold raw1074 raw1075; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4309 = raw1075Labels := by decide +kernel
    rw [ha, hj, canonical1075 B hB]
  have hc1 : mixedMoment B raw1074 (Fin.cases (1 : Fin 2) singletonSmall4309) =
      mixedMoment B node1573 node1573Labels := by
    have ha : raw1074 = raw1076 := by apply Matrix.ext; unfold raw1074 raw1076; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4309 = raw1076Labels := by decide +kernel
    rw [ha, hj, canonical1076 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4310 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4310 node4310Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node888 node888Labels + mixedMoment B node1564 node1564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1077 singletonSmall4310
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4310) = raw1077Labels := by decide +kernel
  rw [hl, canonical1077 B hB] at h
  have hc0 : mixedMoment B raw1077 (Fin.cases (0 : Fin 2) singletonSmall4310) =
      mixedMoment B node888 node888Labels := by
    have ha : raw1077 = raw1078 := by apply Matrix.ext; unfold raw1077 raw1078; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4310 = raw1078Labels := by decide +kernel
    rw [ha, hj, canonical1078 B hB]
  have hc1 : mixedMoment B raw1077 (Fin.cases (1 : Fin 2) singletonSmall4310) =
      mixedMoment B node1564 node1564Labels := by
    have ha : raw1077 = raw1079 := by apply Matrix.ext; unfold raw1077 raw1079; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4310 = raw1079Labels := by decide +kernel
    rw [ha, hj, canonical1079 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4313 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4313 node4313Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node891 node891Labels + mixedMoment B node1565 node1565Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1080 singletonSmall4313
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4313) = raw1080Labels := by decide +kernel
  rw [hl, canonical1080 B hB] at h
  have hc0 : mixedMoment B raw1080 (Fin.cases (0 : Fin 2) singletonSmall4313) =
      mixedMoment B node891 node891Labels := by
    have ha : raw1080 = raw1081 := by apply Matrix.ext; unfold raw1080 raw1081; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4313 = raw1081Labels := by decide +kernel
    rw [ha, hj, canonical1081 B hB]
  have hc1 : mixedMoment B raw1080 (Fin.cases (1 : Fin 2) singletonSmall4313) =
      mixedMoment B node1565 node1565Labels := by
    have ha : raw1080 = raw1082 := by apply Matrix.ext; unfold raw1080 raw1082; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4313 = raw1082Labels := by decide +kernel
    rw [ha, hj, canonical1082 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4314 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4314 node4314Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node892 node892Labels + mixedMoment B node1575 node1575Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1083 singletonSmall4314
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4314) = raw1083Labels := by decide +kernel
  rw [hl, canonical1083 B hB] at h
  have hc0 : mixedMoment B raw1083 (Fin.cases (0 : Fin 2) singletonSmall4314) =
      mixedMoment B node892 node892Labels := by
    have ha : raw1083 = raw1084 := by apply Matrix.ext; unfold raw1083 raw1084; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4314 = raw1084Labels := by decide +kernel
    rw [ha, hj, canonical1084 B hB]
  have hc1 : mixedMoment B raw1083 (Fin.cases (1 : Fin 2) singletonSmall4314) =
      mixedMoment B node1575 node1575Labels := by
    have ha : raw1083 = raw1085 := by apply Matrix.ext; unfold raw1083 raw1085; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4314 = raw1085Labels := by decide +kernel
    rw [ha, hj, canonical1085 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4315 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4315 node4315Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node893 node893Labels + mixedMoment B node1578 node1578Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1086 singletonSmall4315
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4315) = raw1086Labels := by decide +kernel
  rw [hl, canonical1086 B hB] at h
  have hc0 : mixedMoment B raw1086 (Fin.cases (0 : Fin 2) singletonSmall4315) =
      mixedMoment B node893 node893Labels := by
    have ha : raw1086 = raw1087 := by apply Matrix.ext; unfold raw1086 raw1087; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4315 = raw1087Labels := by decide +kernel
    rw [ha, hj, canonical1087 B hB]
  have hc1 : mixedMoment B raw1086 (Fin.cases (1 : Fin 2) singletonSmall4315) =
      mixedMoment B node1578 node1578Labels := by
    have ha : raw1086 = raw1088 := by apply Matrix.ext; unfold raw1086 raw1088; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4315 = raw1088Labels := by decide +kernel
    rw [ha, hj, canonical1088 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4316 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4316 node4316Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node894 node894Labels + mixedMoment B node961 node961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1089 singletonSmall4316
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4316) = raw1089Labels := by decide +kernel
  rw [hl, canonical1089 B hB] at h
  have hc0 : mixedMoment B raw1089 (Fin.cases (0 : Fin 2) singletonSmall4316) =
      mixedMoment B node894 node894Labels := by
    have ha : raw1089 = raw1090 := by apply Matrix.ext; unfold raw1089 raw1090; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4316 = raw1090Labels := by decide +kernel
    rw [ha, hj, canonical1090 B hB]
  have hc1 : mixedMoment B raw1089 (Fin.cases (1 : Fin 2) singletonSmall4316) =
      mixedMoment B node961 node961Labels := by
    have ha : raw1089 = raw1091 := by apply Matrix.ext; unfold raw1089 raw1091; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4316 = raw1091Labels := by decide +kernel
    rw [ha, hj, canonical1091 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4319 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4319 node4319Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node897 node897Labels + mixedMoment B node1577 node1577Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1092 singletonSmall4319
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4319) = raw1092Labels := by decide +kernel
  rw [hl, canonical1092 B hB] at h
  have hc0 : mixedMoment B raw1092 (Fin.cases (0 : Fin 2) singletonSmall4319) =
      mixedMoment B node897 node897Labels := by
    have ha : raw1092 = raw1093 := by apply Matrix.ext; unfold raw1092 raw1093; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4319 = raw1093Labels := by decide +kernel
    rw [ha, hj, canonical1093 B hB]
  have hc1 : mixedMoment B raw1092 (Fin.cases (1 : Fin 2) singletonSmall4319) =
      mixedMoment B node1577 node1577Labels := by
    have ha : raw1092 = raw1094 := by apply Matrix.ext; unfold raw1092 raw1094; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4319 = raw1094Labels := by decide +kernel
    rw [ha, hj, canonical1094 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4320 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4320 node4320Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node898 node898Labels + mixedMoment B node1586 node1586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1095 singletonSmall4320
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4320) = raw1095Labels := by decide +kernel
  rw [hl, canonical1095 B hB] at h
  have hc0 : mixedMoment B raw1095 (Fin.cases (0 : Fin 2) singletonSmall4320) =
      mixedMoment B node898 node898Labels := by
    have ha : raw1095 = raw1096 := by apply Matrix.ext; unfold raw1095 raw1096; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4320 = raw1096Labels := by decide +kernel
    rw [ha, hj, canonical1096 B hB]
  have hc1 : mixedMoment B raw1095 (Fin.cases (1 : Fin 2) singletonSmall4320) =
      mixedMoment B node1586 node1586Labels := by
    have ha : raw1095 = raw1097 := by apply Matrix.ext; unfold raw1095 raw1097; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4320 = raw1097Labels := by decide +kernel
    rw [ha, hj, canonical1097 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4321 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4321 node4321Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node899 node899Labels + mixedMoment B node1587 node1587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1098 singletonSmall4321
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4321) = raw1098Labels := by decide +kernel
  rw [hl, canonical1098 B hB] at h
  have hc0 : mixedMoment B raw1098 (Fin.cases (0 : Fin 2) singletonSmall4321) =
      mixedMoment B node899 node899Labels := by
    have ha : raw1098 = raw1099 := by apply Matrix.ext; unfold raw1098 raw1099; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4321 = raw1099Labels := by decide +kernel
    rw [ha, hj, canonical1099 B hB]
  have hc1 : mixedMoment B raw1098 (Fin.cases (1 : Fin 2) singletonSmall4321) =
      mixedMoment B node1587 node1587Labels := by
    have ha : raw1098 = raw1100 := by apply Matrix.ext; unfold raw1098 raw1100; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4321 = raw1100Labels := by decide +kernel
    rw [ha, hj, canonical1100 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4322 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4322 node4322Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node900 node900Labels + mixedMoment B node1588 node1588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1101 singletonSmall4322
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4322) = raw1101Labels := by decide +kernel
  rw [hl, canonical1101 B hB] at h
  have hc0 : mixedMoment B raw1101 (Fin.cases (0 : Fin 2) singletonSmall4322) =
      mixedMoment B node900 node900Labels := by
    have ha : raw1101 = raw1102 := by apply Matrix.ext; unfold raw1101 raw1102; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4322 = raw1102Labels := by decide +kernel
    rw [ha, hj, canonical1102 B hB]
  have hc1 : mixedMoment B raw1101 (Fin.cases (1 : Fin 2) singletonSmall4322) =
      mixedMoment B node1588 node1588Labels := by
    have ha : raw1101 = raw1103 := by apply Matrix.ext; unfold raw1101 raw1103; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4322 = raw1103Labels := by decide +kernel
    rw [ha, hj, canonical1103 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4323 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4323 node4323Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node901 node901Labels + mixedMoment B node1589 node1589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1104 singletonSmall4323
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4323) = raw1104Labels := by decide +kernel
  rw [hl, canonical1104 B hB] at h
  have hc0 : mixedMoment B raw1104 (Fin.cases (0 : Fin 2) singletonSmall4323) =
      mixedMoment B node901 node901Labels := by
    have ha : raw1104 = raw1105 := by apply Matrix.ext; unfold raw1104 raw1105; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4323 = raw1105Labels := by decide +kernel
    rw [ha, hj, canonical1105 B hB]
  have hc1 : mixedMoment B raw1104 (Fin.cases (1 : Fin 2) singletonSmall4323) =
      mixedMoment B node1589 node1589Labels := by
    have ha : raw1104 = raw1106 := by apply Matrix.ext; unfold raw1104 raw1106; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4323 = raw1106Labels := by decide +kernel
    rw [ha, hj, canonical1106 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4324 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4324 node4324Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node902 node902Labels + mixedMoment B node1590 node1590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1107 singletonSmall4324
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4324) = raw1107Labels := by decide +kernel
  rw [hl, canonical1107 B hB] at h
  have hc0 : mixedMoment B raw1107 (Fin.cases (0 : Fin 2) singletonSmall4324) =
      mixedMoment B node902 node902Labels := by
    have ha : raw1107 = raw1108 := by apply Matrix.ext; unfold raw1107 raw1108; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4324 = raw1108Labels := by decide +kernel
    rw [ha, hj, canonical1108 B hB]
  have hc1 : mixedMoment B raw1107 (Fin.cases (1 : Fin 2) singletonSmall4324) =
      mixedMoment B node1590 node1590Labels := by
    have ha : raw1107 = raw1109 := by apply Matrix.ext; unfold raw1107 raw1109; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4324 = raw1109Labels := by decide +kernel
    rw [ha, hj, canonical1109 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4325 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4325 node4325Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node903 node903Labels + mixedMoment B node1591 node1591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1110 singletonSmall4325
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4325) = raw1110Labels := by decide +kernel
  rw [hl, canonical1110 B hB] at h
  have hc0 : mixedMoment B raw1110 (Fin.cases (0 : Fin 2) singletonSmall4325) =
      mixedMoment B node903 node903Labels := by
    have ha : raw1110 = raw1111 := by apply Matrix.ext; unfold raw1110 raw1111; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4325 = raw1111Labels := by decide +kernel
    rw [ha, hj, canonical1111 B hB]
  have hc1 : mixedMoment B raw1110 (Fin.cases (1 : Fin 2) singletonSmall4325) =
      mixedMoment B node1591 node1591Labels := by
    have ha : raw1110 = raw1112 := by apply Matrix.ext; unfold raw1110 raw1112; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4325 = raw1112Labels := by decide +kernel
    rw [ha, hj, canonical1112 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4337 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4337 node4337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node915 node915Labels + mixedMoment B node1632 node1632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1113 singletonSmall4337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4337) = raw1113Labels := by decide +kernel
  rw [hl, canonical1113 B hB] at h
  have hc0 : mixedMoment B raw1113 (Fin.cases (0 : Fin 2) singletonSmall4337) =
      mixedMoment B node915 node915Labels := by
    have ha : raw1113 = raw1114 := by apply Matrix.ext; unfold raw1113 raw1114; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4337 = raw1114Labels := by decide +kernel
    rw [ha, hj, canonical1114 B hB]
  have hc1 : mixedMoment B raw1113 (Fin.cases (1 : Fin 2) singletonSmall4337) =
      mixedMoment B node1632 node1632Labels := by
    have ha : raw1113 = raw1115 := by apply Matrix.ext; unfold raw1113 raw1115; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4337 = raw1115Labels := by decide +kernel
    rw [ha, hj, canonical1115 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4338 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4338 node4338Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node916 node916Labels + mixedMoment B node1633 node1633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1116 singletonSmall4338
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4338) = raw1116Labels := by decide +kernel
  rw [hl, canonical1116 B hB] at h
  have hc0 : mixedMoment B raw1116 (Fin.cases (0 : Fin 2) singletonSmall4338) =
      mixedMoment B node916 node916Labels := by
    have ha : raw1116 = raw1117 := by apply Matrix.ext; unfold raw1116 raw1117; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4338 = raw1117Labels := by decide +kernel
    rw [ha, hj, canonical1117 B hB]
  have hc1 : mixedMoment B raw1116 (Fin.cases (1 : Fin 2) singletonSmall4338) =
      mixedMoment B node1633 node1633Labels := by
    have ha : raw1116 = raw1118 := by apply Matrix.ext; unfold raw1116 raw1118; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4338 = raw1118Labels := by decide +kernel
    rw [ha, hj, canonical1118 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4339 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4339 node4339Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node917 node917Labels + mixedMoment B node1634 node1634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1119 singletonSmall4339
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4339) = raw1119Labels := by decide +kernel
  rw [hl, canonical1119 B hB] at h
  have hc0 : mixedMoment B raw1119 (Fin.cases (0 : Fin 2) singletonSmall4339) =
      mixedMoment B node917 node917Labels := by
    have ha : raw1119 = raw1120 := by apply Matrix.ext; unfold raw1119 raw1120; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4339 = raw1120Labels := by decide +kernel
    rw [ha, hj, canonical1120 B hB]
  have hc1 : mixedMoment B raw1119 (Fin.cases (1 : Fin 2) singletonSmall4339) =
      mixedMoment B node1634 node1634Labels := by
    have ha : raw1119 = raw1121 := by apply Matrix.ext; unfold raw1119 raw1121; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4339 = raw1121Labels := by decide +kernel
    rw [ha, hj, canonical1121 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4341 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4341 node4341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node919 node919Labels + mixedMoment B node1664 node1664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1122 singletonSmall4341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4341) = raw1122Labels := by decide +kernel
  rw [hl, canonical1122 B hB] at h
  have hc0 : mixedMoment B raw1122 (Fin.cases (0 : Fin 2) singletonSmall4341) =
      mixedMoment B node919 node919Labels := by
    have ha : raw1122 = raw1123 := by apply Matrix.ext; unfold raw1122 raw1123; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4341 = raw1123Labels := by decide +kernel
    rw [ha, hj, canonical1123 B hB]
  have hc1 : mixedMoment B raw1122 (Fin.cases (1 : Fin 2) singletonSmall4341) =
      mixedMoment B node1664 node1664Labels := by
    have ha : raw1122 = raw1124 := by apply Matrix.ext; unfold raw1122 raw1124; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4341 = raw1124Labels := by decide +kernel
    rw [ha, hj, canonical1124 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4343 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4343 node4343Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node921 node921Labels + mixedMoment B node1666 node1666Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1125 singletonSmall4343
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4343) = raw1125Labels := by decide +kernel
  rw [hl, canonical1125 B hB] at h
  have hc0 : mixedMoment B raw1125 (Fin.cases (0 : Fin 2) singletonSmall4343) =
      mixedMoment B node921 node921Labels := by
    have ha : raw1125 = raw1126 := by apply Matrix.ext; unfold raw1125 raw1126; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4343 = raw1126Labels := by decide +kernel
    rw [ha, hj, canonical1126 B hB]
  have hc1 : mixedMoment B raw1125 (Fin.cases (1 : Fin 2) singletonSmall4343) =
      mixedMoment B node1666 node1666Labels := by
    have ha : raw1125 = raw1127 := by apply Matrix.ext; unfold raw1125 raw1127; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4343 = raw1127Labels := by decide +kernel
    rw [ha, hj, canonical1127 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4344 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4346 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4346 node4346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node924 node924Labels + mixedMoment B node1674 node1674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1131 singletonSmall4346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4346) = raw1131Labels := by decide +kernel
  rw [hl, canonical1131 B hB] at h
  have hc0 : mixedMoment B raw1131 (Fin.cases (0 : Fin 2) singletonSmall4346) =
      mixedMoment B node924 node924Labels := by
    have ha : raw1131 = raw1132 := by apply Matrix.ext; unfold raw1131 raw1132; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4346 = raw1132Labels := by decide +kernel
    rw [ha, hj, canonical1132 B hB]
  have hc1 : mixedMoment B raw1131 (Fin.cases (1 : Fin 2) singletonSmall4346) =
      mixedMoment B node1674 node1674Labels := by
    have ha : raw1131 = raw1133 := by apply Matrix.ext; unfold raw1131 raw1133; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4346 = raw1133Labels := by decide +kernel
    rw [ha, hj, canonical1133 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4349 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4350 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4350 node4350Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node928 node928Labels + mixedMoment B node1677 node1677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1137 singletonSmall4350
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4350) = raw1137Labels := by decide +kernel
  rw [hl, canonical1137 B hB] at h
  have hc0 : mixedMoment B raw1137 (Fin.cases (0 : Fin 2) singletonSmall4350) =
      mixedMoment B node928 node928Labels := by
    have ha : raw1137 = raw1138 := by apply Matrix.ext; unfold raw1137 raw1138; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4350 = raw1138Labels := by decide +kernel
    rw [ha, hj, canonical1138 B hB]
  have hc1 : mixedMoment B raw1137 (Fin.cases (1 : Fin 2) singletonSmall4350) =
      mixedMoment B node1677 node1677Labels := by
    have ha : raw1137 = raw1139 := by apply Matrix.ext; unfold raw1137 raw1139; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4350 = raw1139Labels := by decide +kernel
    rw [ha, hj, canonical1139 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4351 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4351 node4351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node929 node929Labels + mixedMoment B node1680 node1680Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1140 singletonSmall4351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4351) = raw1140Labels := by decide +kernel
  rw [hl, canonical1140 B hB] at h
  have hc0 : mixedMoment B raw1140 (Fin.cases (0 : Fin 2) singletonSmall4351) =
      mixedMoment B node929 node929Labels := by
    have ha : raw1140 = raw1141 := by apply Matrix.ext; unfold raw1140 raw1141; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4351 = raw1141Labels := by decide +kernel
    rw [ha, hj, canonical1141 B hB]
  have hc1 : mixedMoment B raw1140 (Fin.cases (1 : Fin 2) singletonSmall4351) =
      mixedMoment B node1680 node1680Labels := by
    have ha : raw1140 = raw1142 := by apply Matrix.ext; unfold raw1140 raw1142; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4351 = raw1142Labels := by decide +kernel
    rw [ha, hj, canonical1142 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
