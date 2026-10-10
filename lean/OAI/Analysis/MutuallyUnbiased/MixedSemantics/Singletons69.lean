import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical10

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4417 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4417 node4417Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node998 node998Labels + mixedMoment B node1600 node1600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1224 singletonSmall4417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4417) = raw1224Labels := by decide +kernel
  rw [hl, canonical1224 B hB] at h
  have hc0 : mixedMoment B raw1224 (Fin.cases (0 : Fin 2) singletonSmall4417) =
      mixedMoment B node998 node998Labels := by
    have ha : raw1224 = raw1225 := by apply Matrix.ext; unfold raw1224 raw1225; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4417 = raw1225Labels := by decide +kernel
    rw [ha, hj, canonical1225 B hB]
  have hc1 : mixedMoment B raw1224 (Fin.cases (1 : Fin 2) singletonSmall4417) =
      mixedMoment B node1600 node1600Labels := by
    have ha : raw1224 = raw1226 := by apply Matrix.ext; unfold raw1224 raw1226; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4417 = raw1226Labels := by decide +kernel
    rw [ha, hj, canonical1226 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4418 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4418 node4418Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node999 node999Labels + mixedMoment B node1602 node1602Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1227 singletonSmall4418
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4418) = raw1227Labels := by decide +kernel
  rw [hl, canonical1227 B hB] at h
  have hc0 : mixedMoment B raw1227 (Fin.cases (0 : Fin 2) singletonSmall4418) =
      mixedMoment B node999 node999Labels := by
    have ha : raw1227 = raw1228 := by apply Matrix.ext; unfold raw1227 raw1228; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4418 = raw1228Labels := by decide +kernel
    rw [ha, hj, canonical1228 B hB]
  have hc1 : mixedMoment B raw1227 (Fin.cases (1 : Fin 2) singletonSmall4418) =
      mixedMoment B node1602 node1602Labels := by
    have ha : raw1227 = raw1229 := by apply Matrix.ext; unfold raw1227 raw1229; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4418 = raw1229Labels := by decide +kernel
    rw [ha, hj, canonical1229 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4419 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4419 node4419Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1000 node1000Labels + mixedMoment B node1605 node1605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1230 singletonSmall4419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4419) = raw1230Labels := by decide +kernel
  rw [hl, canonical1230 B hB] at h
  have hc0 : mixedMoment B raw1230 (Fin.cases (0 : Fin 2) singletonSmall4419) =
      mixedMoment B node1000 node1000Labels := by
    have ha : raw1230 = raw1231 := by apply Matrix.ext; unfold raw1230 raw1231; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4419 = raw1231Labels := by decide +kernel
    rw [ha, hj, canonical1231 B hB]
  have hc1 : mixedMoment B raw1230 (Fin.cases (1 : Fin 2) singletonSmall4419) =
      mixedMoment B node1605 node1605Labels := by
    have ha : raw1230 = raw1232 := by apply Matrix.ext; unfold raw1230 raw1232; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4419 = raw1232Labels := by decide +kernel
    rw [ha, hj, canonical1232 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4421 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4421 node4421Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1002 node1002Labels + mixedMoment B node1002 node1002Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1233 singletonSmall4421
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4421) = raw1233Labels := by decide +kernel
  rw [hl, canonical1233 B hB] at h
  have hc0 : mixedMoment B raw1233 (Fin.cases (0 : Fin 2) singletonSmall4421) =
      mixedMoment B node1002 node1002Labels := by
    have ha : raw1233 = raw1234 := by apply Matrix.ext; unfold raw1233 raw1234; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4421 = raw1234Labels := by decide +kernel
    rw [ha, hj, canonical1234 B hB]
  have hc1 : mixedMoment B raw1233 (Fin.cases (1 : Fin 2) singletonSmall4421) =
      mixedMoment B node1002 node1002Labels := by
    have ha : raw1233 = raw1235 := by apply Matrix.ext; unfold raw1233 raw1235; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4421 = raw1235Labels := by decide +kernel
    rw [ha, hj, canonical1235 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4424 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4424 node4424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1005 node1005Labels + mixedMoment B node1623 node1623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1236 singletonSmall4424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4424) = raw1236Labels := by decide +kernel
  rw [hl, canonical1236 B hB] at h
  have hc0 : mixedMoment B raw1236 (Fin.cases (0 : Fin 2) singletonSmall4424) =
      mixedMoment B node1005 node1005Labels := by
    have ha : raw1236 = raw1237 := by apply Matrix.ext; unfold raw1236 raw1237; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4424 = raw1237Labels := by decide +kernel
    rw [ha, hj, canonical1237 B hB]
  have hc1 : mixedMoment B raw1236 (Fin.cases (1 : Fin 2) singletonSmall4424) =
      mixedMoment B node1623 node1623Labels := by
    have ha : raw1236 = raw1238 := by apply Matrix.ext; unfold raw1236 raw1238; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4424 = raw1238Labels := by decide +kernel
    rw [ha, hj, canonical1238 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4428 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4428 node4428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1009 node1009Labels + mixedMoment B node1630 node1630Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1239 singletonSmall4428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4428) = raw1239Labels := by decide +kernel
  rw [hl, canonical1239 B hB] at h
  have hc0 : mixedMoment B raw1239 (Fin.cases (0 : Fin 2) singletonSmall4428) =
      mixedMoment B node1009 node1009Labels := by
    have ha : raw1239 = raw1240 := by apply Matrix.ext; unfold raw1239 raw1240; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4428 = raw1240Labels := by decide +kernel
    rw [ha, hj, canonical1240 B hB]
  have hc1 : mixedMoment B raw1239 (Fin.cases (1 : Fin 2) singletonSmall4428) =
      mixedMoment B node1630 node1630Labels := by
    have ha : raw1239 = raw1241 := by apply Matrix.ext; unfold raw1239 raw1241; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4428 = raw1241Labels := by decide +kernel
    rw [ha, hj, canonical1241 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4431 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4431 node4431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1012 node1012Labels + mixedMoment B node1627 node1627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1242 singletonSmall4431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4431) = raw1242Labels := by decide +kernel
  rw [hl, canonical1242 B hB] at h
  have hc0 : mixedMoment B raw1242 (Fin.cases (0 : Fin 2) singletonSmall4431) =
      mixedMoment B node1012 node1012Labels := by
    have ha : raw1242 = raw1243 := by apply Matrix.ext; unfold raw1242 raw1243; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4431 = raw1243Labels := by decide +kernel
    rw [ha, hj, canonical1243 B hB]
  have hc1 : mixedMoment B raw1242 (Fin.cases (1 : Fin 2) singletonSmall4431) =
      mixedMoment B node1627 node1627Labels := by
    have ha : raw1242 = raw1244 := by apply Matrix.ext; unfold raw1242 raw1244; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4431 = raw1244Labels := by decide +kernel
    rw [ha, hj, canonical1244 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4451 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4451 node4451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1034 node1034Labels + mixedMoment B node1644 node1644Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1245 singletonSmall4451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4451) = raw1245Labels := by decide +kernel
  rw [hl, canonical1245 B hB] at h
  have hc0 : mixedMoment B raw1245 (Fin.cases (0 : Fin 2) singletonSmall4451) =
      mixedMoment B node1034 node1034Labels := by
    have ha : raw1245 = raw1246 := by apply Matrix.ext; unfold raw1245 raw1246; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4451 = raw1246Labels := by decide +kernel
    rw [ha, hj, canonical1246 B hB]
  have hc1 : mixedMoment B raw1245 (Fin.cases (1 : Fin 2) singletonSmall4451) =
      mixedMoment B node1644 node1644Labels := by
    have ha : raw1245 = raw1247 := by apply Matrix.ext; unfold raw1245 raw1247; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4451 = raw1247Labels := by decide +kernel
    rw [ha, hj, canonical1247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4452 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4454 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4454 node4454Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1037 node1037Labels + mixedMoment B node1647 node1647Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1251 singletonSmall4454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4454) = raw1251Labels := by decide +kernel
  rw [hl, canonical1251 B hB] at h
  have hc0 : mixedMoment B raw1251 (Fin.cases (0 : Fin 2) singletonSmall4454) =
      mixedMoment B node1037 node1037Labels := by
    have ha : raw1251 = raw1252 := by apply Matrix.ext; unfold raw1251 raw1252; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4454 = raw1252Labels := by decide +kernel
    rw [ha, hj, canonical1252 B hB]
  have hc1 : mixedMoment B raw1251 (Fin.cases (1 : Fin 2) singletonSmall4454) =
      mixedMoment B node1647 node1647Labels := by
    have ha : raw1251 = raw1253 := by apply Matrix.ext; unfold raw1251 raw1253; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4454 = raw1253Labels := by decide +kernel
    rw [ha, hj, canonical1253 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4456 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4456 node4456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1039 node1039Labels + mixedMoment B node1706 node1706Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1254 singletonSmall4456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4456) = raw1254Labels := by decide +kernel
  rw [hl, canonical1254 B hB] at h
  have hc0 : mixedMoment B raw1254 (Fin.cases (0 : Fin 2) singletonSmall4456) =
      mixedMoment B node1039 node1039Labels := by
    have ha : raw1254 = raw1255 := by apply Matrix.ext; unfold raw1254 raw1255; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4456 = raw1255Labels := by decide +kernel
    rw [ha, hj, canonical1255 B hB]
  have hc1 : mixedMoment B raw1254 (Fin.cases (1 : Fin 2) singletonSmall4456) =
      mixedMoment B node1706 node1706Labels := by
    have ha : raw1254 = raw1256 := by apply Matrix.ext; unfold raw1254 raw1256; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4456 = raw1256Labels := by decide +kernel
    rw [ha, hj, canonical1256 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4457 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4458 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4460 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4461 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4463 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4466 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4467 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4468 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
