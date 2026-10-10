import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical10

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4489 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4489 node4489Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1073 node1073Labels + mixedMoment B node1648 node1648Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1281 singletonSmall4489
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4489) = raw1281Labels := by decide +kernel
  rw [hl, canonical1281 B hB] at h
  have hc0 : mixedMoment B raw1281 (Fin.cases (0 : Fin 2) singletonSmall4489) =
      mixedMoment B node1073 node1073Labels := by
    have ha : raw1281 = raw1282 := by apply Matrix.ext; unfold raw1281 raw1282; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4489 = raw1282Labels := by decide +kernel
    rw [ha, hj, canonical1282 B hB]
  have hc1 : mixedMoment B raw1281 (Fin.cases (1 : Fin 2) singletonSmall4489) =
      mixedMoment B node1648 node1648Labels := by
    have ha : raw1281 = raw1283 := by apply Matrix.ext; unfold raw1281 raw1283; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4489 = raw1283Labels := by decide +kernel
    rw [ha, hj, canonical1283 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4490 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4490 node4490Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1074 node1074Labels + mixedMoment B node1650 node1650Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1284 singletonSmall4490
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4490) = raw1284Labels := by decide +kernel
  rw [hl, canonical1284 B hB] at h
  have hc0 : mixedMoment B raw1284 (Fin.cases (0 : Fin 2) singletonSmall4490) =
      mixedMoment B node1074 node1074Labels := by
    have ha : raw1284 = raw1285 := by apply Matrix.ext; unfold raw1284 raw1285; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4490 = raw1285Labels := by decide +kernel
    rw [ha, hj, canonical1285 B hB]
  have hc1 : mixedMoment B raw1284 (Fin.cases (1 : Fin 2) singletonSmall4490) =
      mixedMoment B node1650 node1650Labels := by
    have ha : raw1284 = raw1286 := by apply Matrix.ext; unfold raw1284 raw1286; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4490 = raw1286Labels := by decide +kernel
    rw [ha, hj, canonical1286 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4491 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4491 node4491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1075 node1075Labels + mixedMoment B node1653 node1653Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1287 singletonSmall4491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4491) = raw1287Labels := by decide +kernel
  rw [hl, canonical1287 B hB] at h
  have hc0 : mixedMoment B raw1287 (Fin.cases (0 : Fin 2) singletonSmall4491) =
      mixedMoment B node1075 node1075Labels := by
    have ha : raw1287 = raw1288 := by apply Matrix.ext; unfold raw1287 raw1288; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4491 = raw1288Labels := by decide +kernel
    rw [ha, hj, canonical1288 B hB]
  have hc1 : mixedMoment B raw1287 (Fin.cases (1 : Fin 2) singletonSmall4491) =
      mixedMoment B node1653 node1653Labels := by
    have ha : raw1287 = raw1289 := by apply Matrix.ext; unfold raw1287 raw1289; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4491 = raw1289Labels := by decide +kernel
    rw [ha, hj, canonical1289 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4493 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4493 node4493Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1077 node1077Labels + mixedMoment B node1077 node1077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1290 singletonSmall4493
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4493) = raw1290Labels := by decide +kernel
  rw [hl, canonical1290 B hB] at h
  have hc0 : mixedMoment B raw1290 (Fin.cases (0 : Fin 2) singletonSmall4493) =
      mixedMoment B node1077 node1077Labels := by
    have ha : raw1290 = raw1291 := by apply Matrix.ext; unfold raw1290 raw1291; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4493 = raw1291Labels := by decide +kernel
    rw [ha, hj, canonical1291 B hB]
  have hc1 : mixedMoment B raw1290 (Fin.cases (1 : Fin 2) singletonSmall4493) =
      mixedMoment B node1077 node1077Labels := by
    have ha : raw1290 = raw1292 := by apply Matrix.ext; unfold raw1290 raw1292; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4493 = raw1292Labels := by decide +kernel
    rw [ha, hj, canonical1292 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4495 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4496 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4496 node4496Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1080 node1080Labels + mixedMoment B node1710 node1710Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1296 singletonSmall4496
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4496) = raw1296Labels := by decide +kernel
  rw [hl, canonical1296 B hB] at h
  have hc0 : mixedMoment B raw1296 (Fin.cases (0 : Fin 2) singletonSmall4496) =
      mixedMoment B node1080 node1080Labels := by
    have ha : raw1296 = raw1297 := by apply Matrix.ext; unfold raw1296 raw1297; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4496 = raw1297Labels := by decide +kernel
    rw [ha, hj, canonical1297 B hB]
  have hc1 : mixedMoment B raw1296 (Fin.cases (1 : Fin 2) singletonSmall4496) =
      mixedMoment B node1710 node1710Labels := by
    have ha : raw1296 = raw1298 := by apply Matrix.ext; unfold raw1296 raw1298; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4496 = raw1298Labels := by decide +kernel
    rw [ha, hj, canonical1298 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4499 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4499 node4499Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1083 node1083Labels + mixedMoment B node1728 node1728Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1299 singletonSmall4499
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4499) = raw1299Labels := by decide +kernel
  rw [hl, canonical1299 B hB] at h
  have hc0 : mixedMoment B raw1299 (Fin.cases (0 : Fin 2) singletonSmall4499) =
      mixedMoment B node1083 node1083Labels := by
    have ha : raw1299 = raw1300 := by apply Matrix.ext; unfold raw1299 raw1300; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4499 = raw1300Labels := by decide +kernel
    rw [ha, hj, canonical1300 B hB]
  have hc1 : mixedMoment B raw1299 (Fin.cases (1 : Fin 2) singletonSmall4499) =
      mixedMoment B node1728 node1728Labels := by
    have ha : raw1299 = raw1301 := by apply Matrix.ext; unfold raw1299 raw1301; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4499 = raw1301Labels := by decide +kernel
    rw [ha, hj, canonical1301 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4503 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4503 node4503Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1087 node1087Labels + mixedMoment B node1739 node1739Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1302 singletonSmall4503
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4503) = raw1302Labels := by decide +kernel
  rw [hl, canonical1302 B hB] at h
  have hc0 : mixedMoment B raw1302 (Fin.cases (0 : Fin 2) singletonSmall4503) =
      mixedMoment B node1087 node1087Labels := by
    have ha : raw1302 = raw1303 := by apply Matrix.ext; unfold raw1302 raw1303; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4503 = raw1303Labels := by decide +kernel
    rw [ha, hj, canonical1303 B hB]
  have hc1 : mixedMoment B raw1302 (Fin.cases (1 : Fin 2) singletonSmall4503) =
      mixedMoment B node1739 node1739Labels := by
    have ha : raw1302 = raw1304 := by apply Matrix.ext; unfold raw1302 raw1304; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4503 = raw1304Labels := by decide +kernel
    rw [ha, hj, canonical1304 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4507 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4507 node4507Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1091 node1091Labels + mixedMoment B node1756 node1756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1305 singletonSmall4507
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4507) = raw1305Labels := by decide +kernel
  rw [hl, canonical1305 B hB] at h
  have hc0 : mixedMoment B raw1305 (Fin.cases (0 : Fin 2) singletonSmall4507) =
      mixedMoment B node1091 node1091Labels := by
    have ha : raw1305 = raw1306 := by apply Matrix.ext; unfold raw1305 raw1306; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4507 = raw1306Labels := by decide +kernel
    rw [ha, hj, canonical1306 B hB]
  have hc1 : mixedMoment B raw1305 (Fin.cases (1 : Fin 2) singletonSmall4507) =
      mixedMoment B node1756 node1756Labels := by
    have ha : raw1305 = raw1307 := by apply Matrix.ext; unfold raw1305 raw1307; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4507 = raw1307Labels := by decide +kernel
    rw [ha, hj, canonical1307 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4510 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4510 node4510Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1094 node1094Labels + mixedMoment B node1741 node1741Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1308 singletonSmall4510
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4510) = raw1308Labels := by decide +kernel
  rw [hl, canonical1308 B hB] at h
  have hc0 : mixedMoment B raw1308 (Fin.cases (0 : Fin 2) singletonSmall4510) =
      mixedMoment B node1094 node1094Labels := by
    have ha : raw1308 = raw1309 := by apply Matrix.ext; unfold raw1308 raw1309; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4510 = raw1309Labels := by decide +kernel
    rw [ha, hj, canonical1309 B hB]
  have hc1 : mixedMoment B raw1308 (Fin.cases (1 : Fin 2) singletonSmall4510) =
      mixedMoment B node1741 node1741Labels := by
    have ha : raw1308 = raw1310 := by apply Matrix.ext; unfold raw1308 raw1310; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4510 = raw1310Labels := by decide +kernel
    rw [ha, hj, canonical1310 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4513 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4513 node4513Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1097 node1097Labels + mixedMoment B node3232 node3232Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1311 singletonSmall4513
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4513) = raw1311Labels := by decide +kernel
  rw [hl, canonical1311 B hB] at h
  have hc0 : mixedMoment B raw1311 (Fin.cases (0 : Fin 2) singletonSmall4513) =
      mixedMoment B node1097 node1097Labels := by
    have ha : raw1311 = raw1312 := by apply Matrix.ext; unfold raw1311 raw1312; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4513 = raw1312Labels := by decide +kernel
    rw [ha, hj, canonical1312 B hB]
  have hc1 : mixedMoment B raw1311 (Fin.cases (1 : Fin 2) singletonSmall4513) =
      mixedMoment B node3232 node3232Labels := by
    have ha : raw1311 = raw1313 := by apply Matrix.ext; unfold raw1311 raw1313; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4513 = raw1313Labels := by decide +kernel
    rw [ha, hj, canonical1313 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4514 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4514 node4514Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1098 node1098Labels + mixedMoment B node1894 node1894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1314 singletonSmall4514
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4514) = raw1314Labels := by decide +kernel
  rw [hl, canonical1314 B hB] at h
  have hc0 : mixedMoment B raw1314 (Fin.cases (0 : Fin 2) singletonSmall4514) =
      mixedMoment B node1098 node1098Labels := by
    have ha : raw1314 = raw1315 := by apply Matrix.ext; unfold raw1314 raw1315; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4514 = raw1315Labels := by decide +kernel
    rw [ha, hj, canonical1315 B hB]
  have hc1 : mixedMoment B raw1314 (Fin.cases (1 : Fin 2) singletonSmall4514) =
      mixedMoment B node1894 node1894Labels := by
    have ha : raw1314 = raw1316 := by apply Matrix.ext; unfold raw1314 raw1316; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4514 = raw1316Labels := by decide +kernel
    rw [ha, hj, canonical1316 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4515 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4515 node4515Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1099 node1099Labels + mixedMoment B node3233 node3233Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1317 singletonSmall4515
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4515) = raw1317Labels := by decide +kernel
  rw [hl, canonical1317 B hB] at h
  have hc0 : mixedMoment B raw1317 (Fin.cases (0 : Fin 2) singletonSmall4515) =
      mixedMoment B node1099 node1099Labels := by
    have ha : raw1317 = raw1318 := by apply Matrix.ext; unfold raw1317 raw1318; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4515 = raw1318Labels := by decide +kernel
    rw [ha, hj, canonical1318 B hB]
  have hc1 : mixedMoment B raw1317 (Fin.cases (1 : Fin 2) singletonSmall4515) =
      mixedMoment B node3233 node3233Labels := by
    have ha : raw1317 = raw1319 := by apply Matrix.ext; unfold raw1317 raw1319; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4515 = raw1319Labels := by decide +kernel
    rw [ha, hj, canonical1319 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4516 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4516 node4516Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1100 node1100Labels + mixedMoment B node3234 node3234Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1320 singletonSmall4516
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4516) = raw1320Labels := by decide +kernel
  rw [hl, canonical1320 B hB] at h
  have hc0 : mixedMoment B raw1320 (Fin.cases (0 : Fin 2) singletonSmall4516) =
      mixedMoment B node1100 node1100Labels := by
    have ha : raw1320 = raw1321 := by apply Matrix.ext; unfold raw1320 raw1321; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4516 = raw1321Labels := by decide +kernel
    rw [ha, hj, canonical1321 B hB]
  have hc1 : mixedMoment B raw1320 (Fin.cases (1 : Fin 2) singletonSmall4516) =
      mixedMoment B node3234 node3234Labels := by
    have ha : raw1320 = raw1322 := by apply Matrix.ext; unfold raw1320 raw1322; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4516 = raw1322Labels := by decide +kernel
    rw [ha, hj, canonical1322 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4517 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4517 node4517Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1101 node1101Labels + mixedMoment B node3235 node3235Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1323 singletonSmall4517
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4517) = raw1323Labels := by decide +kernel
  rw [hl, canonical1323 B hB] at h
  have hc0 : mixedMoment B raw1323 (Fin.cases (0 : Fin 2) singletonSmall4517) =
      mixedMoment B node1101 node1101Labels := by
    have ha : raw1323 = raw1324 := by apply Matrix.ext; unfold raw1323 raw1324; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4517 = raw1324Labels := by decide +kernel
    rw [ha, hj, canonical1324 B hB]
  have hc1 : mixedMoment B raw1323 (Fin.cases (1 : Fin 2) singletonSmall4517) =
      mixedMoment B node3235 node3235Labels := by
    have ha : raw1323 = raw1325 := by apply Matrix.ext; unfold raw1323 raw1325; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4517 = raw1325Labels := by decide +kernel
    rw [ha, hj, canonical1325 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4518 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4518 node4518Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1102 node1102Labels + mixedMoment B node3236 node3236Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1326 singletonSmall4518
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4518) = raw1326Labels := by decide +kernel
  rw [hl, canonical1326 B hB] at h
  have hc0 : mixedMoment B raw1326 (Fin.cases (0 : Fin 2) singletonSmall4518) =
      mixedMoment B node1102 node1102Labels := by
    have ha : raw1326 = raw1327 := by apply Matrix.ext; unfold raw1326 raw1327; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4518 = raw1327Labels := by decide +kernel
    rw [ha, hj, canonical1327 B hB]
  have hc1 : mixedMoment B raw1326 (Fin.cases (1 : Fin 2) singletonSmall4518) =
      mixedMoment B node3236 node3236Labels := by
    have ha : raw1326 = raw1328 := by apply Matrix.ext; unfold raw1326 raw1328; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4518 = raw1328Labels := by decide +kernel
    rw [ha, hj, canonical1328 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4519 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4519 node4519Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1103 node1103Labels + mixedMoment B node1858 node1858Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1329 singletonSmall4519
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4519) = raw1329Labels := by decide +kernel
  rw [hl, canonical1329 B hB] at h
  have hc0 : mixedMoment B raw1329 (Fin.cases (0 : Fin 2) singletonSmall4519) =
      mixedMoment B node1103 node1103Labels := by
    have ha : raw1329 = raw1330 := by apply Matrix.ext; unfold raw1329 raw1330; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4519 = raw1330Labels := by decide +kernel
    rw [ha, hj, canonical1330 B hB]
  have hc1 : mixedMoment B raw1329 (Fin.cases (1 : Fin 2) singletonSmall4519) =
      mixedMoment B node1858 node1858Labels := by
    have ha : raw1329 = raw1331 := by apply Matrix.ext; unfold raw1329 raw1331; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4519 = raw1331Labels := by decide +kernel
    rw [ha, hj, canonical1331 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4520 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4520 node4520Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1104 node1104Labels + mixedMoment B node3237 node3237Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1332 singletonSmall4520
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4520) = raw1332Labels := by decide +kernel
  rw [hl, canonical1332 B hB] at h
  have hc0 : mixedMoment B raw1332 (Fin.cases (0 : Fin 2) singletonSmall4520) =
      mixedMoment B node1104 node1104Labels := by
    have ha : raw1332 = raw1333 := by apply Matrix.ext; unfold raw1332 raw1333; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4520 = raw1333Labels := by decide +kernel
    rw [ha, hj, canonical1333 B hB]
  have hc1 : mixedMoment B raw1332 (Fin.cases (1 : Fin 2) singletonSmall4520) =
      mixedMoment B node3237 node3237Labels := by
    have ha : raw1332 = raw1334 := by apply Matrix.ext; unfold raw1332 raw1334; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4520 = raw1334Labels := by decide +kernel
    rw [ha, hj, canonical1334 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4521 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4521 node4521Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1105 node1105Labels + mixedMoment B node1887 node1887Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1335 singletonSmall4521
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4521) = raw1335Labels := by decide +kernel
  rw [hl, canonical1335 B hB] at h
  have hc0 : mixedMoment B raw1335 (Fin.cases (0 : Fin 2) singletonSmall4521) =
      mixedMoment B node1105 node1105Labels := by
    have ha : raw1335 = raw1336 := by apply Matrix.ext; unfold raw1335 raw1336; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4521 = raw1336Labels := by decide +kernel
    rw [ha, hj, canonical1336 B hB]
  have hc1 : mixedMoment B raw1335 (Fin.cases (1 : Fin 2) singletonSmall4521) =
      mixedMoment B node1887 node1887Labels := by
    have ha : raw1335 = raw1337 := by apply Matrix.ext; unfold raw1335 raw1337; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4521 = raw1337Labels := by decide +kernel
    rw [ha, hj, canonical1337 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4522 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4522 node4522Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1106 node1106Labels + mixedMoment B node3249 node3249Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1338 singletonSmall4522
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4522) = raw1338Labels := by decide +kernel
  rw [hl, canonical1338 B hB] at h
  have hc0 : mixedMoment B raw1338 (Fin.cases (0 : Fin 2) singletonSmall4522) =
      mixedMoment B node1106 node1106Labels := by
    have ha : raw1338 = raw1339 := by apply Matrix.ext; unfold raw1338 raw1339; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4522 = raw1339Labels := by decide +kernel
    rw [ha, hj, canonical1339 B hB]
  have hc1 : mixedMoment B raw1338 (Fin.cases (1 : Fin 2) singletonSmall4522) =
      mixedMoment B node3249 node3249Labels := by
    have ha : raw1338 = raw1340 := by apply Matrix.ext; unfold raw1338 raw1340; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4522 = raw1340Labels := by decide +kernel
    rw [ha, hj, canonical1340 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4523 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4523 node4523Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1107 node1107Labels + mixedMoment B node3250 node3250Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1341 singletonSmall4523
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4523) = raw1341Labels := by decide +kernel
  rw [hl, canonical1341 B hB] at h
  have hc0 : mixedMoment B raw1341 (Fin.cases (0 : Fin 2) singletonSmall4523) =
      mixedMoment B node1107 node1107Labels := by
    have ha : raw1341 = raw1342 := by apply Matrix.ext; unfold raw1341 raw1342; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4523 = raw1342Labels := by decide +kernel
    rw [ha, hj, canonical1342 B hB]
  have hc1 : mixedMoment B raw1341 (Fin.cases (1 : Fin 2) singletonSmall4523) =
      mixedMoment B node3250 node3250Labels := by
    have ha : raw1341 = raw1343 := by apply Matrix.ext; unfold raw1341 raw1343; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4523 = raw1343Labels := by decide +kernel
    rw [ha, hj, canonical1343 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4524 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4524 node4524Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1108 node1108Labels + mixedMoment B node3251 node3251Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1344 singletonSmall4524
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4524) = raw1344Labels := by decide +kernel
  rw [hl, canonical1344 B hB] at h
  have hc0 : mixedMoment B raw1344 (Fin.cases (0 : Fin 2) singletonSmall4524) =
      mixedMoment B node1108 node1108Labels := by
    have ha : raw1344 = raw1345 := by apply Matrix.ext; unfold raw1344 raw1345; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4524 = raw1345Labels := by decide +kernel
    rw [ha, hj, canonical1345 B hB]
  have hc1 : mixedMoment B raw1344 (Fin.cases (1 : Fin 2) singletonSmall4524) =
      mixedMoment B node3251 node3251Labels := by
    have ha : raw1344 = raw1346 := by apply Matrix.ext; unfold raw1344 raw1346; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4524 = raw1346Labels := by decide +kernel
    rw [ha, hj, canonical1346 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4525 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4525 node4525Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1109 node1109Labels + mixedMoment B node1849 node1849Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1347 singletonSmall4525
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4525) = raw1347Labels := by decide +kernel
  rw [hl, canonical1347 B hB] at h
  have hc0 : mixedMoment B raw1347 (Fin.cases (0 : Fin 2) singletonSmall4525) =
      mixedMoment B node1109 node1109Labels := by
    have ha : raw1347 = raw1348 := by apply Matrix.ext; unfold raw1347 raw1348; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4525 = raw1348Labels := by decide +kernel
    rw [ha, hj, canonical1348 B hB]
  have hc1 : mixedMoment B raw1347 (Fin.cases (1 : Fin 2) singletonSmall4525) =
      mixedMoment B node1849 node1849Labels := by
    have ha : raw1347 = raw1349 := by apply Matrix.ext; unfold raw1347 raw1349; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4525 = raw1349Labels := by decide +kernel
    rw [ha, hj, canonical1349 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4526 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4526 node4526Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1110 node1110Labels + mixedMoment B node3252 node3252Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1350 singletonSmall4526
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4526) = raw1350Labels := by decide +kernel
  rw [hl, canonical1350 B hB] at h
  have hc0 : mixedMoment B raw1350 (Fin.cases (0 : Fin 2) singletonSmall4526) =
      mixedMoment B node1110 node1110Labels := by
    have ha : raw1350 = raw1351 := by apply Matrix.ext; unfold raw1350 raw1351; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4526 = raw1351Labels := by decide +kernel
    rw [ha, hj, canonical1351 B hB]
  have hc1 : mixedMoment B raw1350 (Fin.cases (1 : Fin 2) singletonSmall4526) =
      mixedMoment B node3252 node3252Labels := by
    have ha : raw1350 = raw1352 := by apply Matrix.ext; unfold raw1350 raw1352; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4526 = raw1352Labels := by decide +kernel
    rw [ha, hj, canonical1352 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4537 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4537 node4537Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1122 node1122Labels + mixedMoment B node3253 node3253Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1353 singletonSmall4537
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4537) = raw1353Labels := by decide +kernel
  rw [hl, canonical1353 B hB] at h
  have hc0 : mixedMoment B raw1353 (Fin.cases (0 : Fin 2) singletonSmall4537) =
      mixedMoment B node1122 node1122Labels := by
    have ha : raw1353 = raw1354 := by apply Matrix.ext; unfold raw1353 raw1354; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4537 = raw1354Labels := by decide +kernel
    rw [ha, hj, canonical1354 B hB]
  have hc1 : mixedMoment B raw1353 (Fin.cases (1 : Fin 2) singletonSmall4537) =
      mixedMoment B node3253 node3253Labels := by
    have ha : raw1353 = raw1355 := by apply Matrix.ext; unfold raw1353 raw1355; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4537 = raw1355Labels := by decide +kernel
    rw [ha, hj, canonical1355 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4538 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4538 node4538Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1123 node1123Labels + mixedMoment B node1937 node1937Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1356 singletonSmall4538
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4538) = raw1356Labels := by decide +kernel
  rw [hl, canonical1356 B hB] at h
  have hc0 : mixedMoment B raw1356 (Fin.cases (0 : Fin 2) singletonSmall4538) =
      mixedMoment B node1123 node1123Labels := by
    have ha : raw1356 = raw1357 := by apply Matrix.ext; unfold raw1356 raw1357; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4538 = raw1357Labels := by decide +kernel
    rw [ha, hj, canonical1357 B hB]
  have hc1 : mixedMoment B raw1356 (Fin.cases (1 : Fin 2) singletonSmall4538) =
      mixedMoment B node1937 node1937Labels := by
    have ha : raw1356 = raw1358 := by apply Matrix.ext; unfold raw1356 raw1358; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4538 = raw1358Labels := by decide +kernel
    rw [ha, hj, canonical1358 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4539 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4539 node4539Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1124 node1124Labels + mixedMoment B node3254 node3254Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1359 singletonSmall4539
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4539) = raw1359Labels := by decide +kernel
  rw [hl, canonical1359 B hB] at h
  have hc0 : mixedMoment B raw1359 (Fin.cases (0 : Fin 2) singletonSmall4539) =
      mixedMoment B node1124 node1124Labels := by
    have ha : raw1359 = raw1360 := by apply Matrix.ext; unfold raw1359 raw1360; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4539 = raw1360Labels := by decide +kernel
    rw [ha, hj, canonical1360 B hB]
  have hc1 : mixedMoment B raw1359 (Fin.cases (1 : Fin 2) singletonSmall4539) =
      mixedMoment B node3254 node3254Labels := by
    have ha : raw1359 = raw1361 := by apply Matrix.ext; unfold raw1359 raw1361; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4539 = raw1361Labels := by decide +kernel
    rw [ha, hj, canonical1361 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4541 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4541 node4541Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1126 node1126Labels + mixedMoment B node3256 node3256Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1362 singletonSmall4541
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4541) = raw1362Labels := by decide +kernel
  rw [hl, canonical1362 B hB] at h
  have hc0 : mixedMoment B raw1362 (Fin.cases (0 : Fin 2) singletonSmall4541) =
      mixedMoment B node1126 node1126Labels := by
    have ha : raw1362 = raw1363 := by apply Matrix.ext; unfold raw1362 raw1363; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4541 = raw1363Labels := by decide +kernel
    rw [ha, hj, canonical1363 B hB]
  have hc1 : mixedMoment B raw1362 (Fin.cases (1 : Fin 2) singletonSmall4541) =
      mixedMoment B node3256 node3256Labels := by
    have ha : raw1362 = raw1364 := by apply Matrix.ext; unfold raw1362 raw1364; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4541 = raw1364Labels := by decide +kernel
    rw [ha, hj, canonical1364 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

def singletonSmall4543 : Fin 2 → Fin 2 := ![0, 1]

theorem singleton4543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4543 node4543Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1128 node1128Labels + mixedMoment B node2184 node2184Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1365 singletonSmall4543
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4543) = raw1365Labels := by decide +kernel
  rw [hl, canonical1365 B hB] at h
  have hc0 : mixedMoment B raw1365 (Fin.cases (0 : Fin 2) singletonSmall4543) =
      mixedMoment B node1128 node1128Labels := by
    have ha : raw1365 = raw1366 := by apply Matrix.ext; unfold raw1365 raw1366; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4543 = raw1366Labels := by decide +kernel
    rw [ha, hj, canonical1366 B hB]
  have hc1 : mixedMoment B raw1365 (Fin.cases (1 : Fin 2) singletonSmall4543) =
      mixedMoment B node2184 node2184Labels := by
    have ha : raw1365 = raw1367 := by apply Matrix.ext; unfold raw1365 raw1367; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4543 = raw1367Labels := by decide +kernel
    rw [ha, hj, canonical1367 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
