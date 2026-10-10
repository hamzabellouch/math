import OAI.Analysis.MutuallyUnbiased.MixedData.Source7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource992 (x : Master → ℝ) : ℝ :=
  (4 : ℝ) * Sparse.eval nodeValue5398 x + ((8 : ℝ) * Sparse.eval nodeValue5403 x + ((2 : ℝ) * Sparse.eval nodeValue5415 x + ((8 : ℝ) * Sparse.eval nodeValue5439 x + ((4 : ℝ) * Sparse.eval nodeValue5448 x + ((4 : ℝ) * Sparse.eval nodeValue5491 x + 0)))))

def numericRow992 : Integer.Sparse Master := [(Sum.inl 0, 1101), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 7, -480), (Sum.inl 23, 720), (Sum.inl 12, 480), (Sum.inl 27, 180), (Sum.inl 1, 5820), (Sum.inr 3784, -51840), (Sum.inr 3789, -51840), (Sum.inr 3810, -51840), (Sum.inr 3885, -51840), (Sum.inr 3895, -12960), (Sum.inr 3902, -51840)]

theorem reindexCheck992 : Integer.Sparse.reindex keyMap MixedData.row992 = numericRow992 := by decide +kernel

theorem numericCheck992 (x : Master → ℝ) : Integer.Sparse.eval numericRow992 x =
    (25920 : ℝ) * reducedSource992 x := by
  norm_num [numericRow992, reducedSource992, Integer.Sparse.eval, Sparse.eval, nodeValue5398, nodeValue5403, nodeValue5415, nodeValue5439, nodeValue5448, nodeValue5491]
  ring

noncomputable def reducedSource993 (x : Master → ℝ) : ℝ :=
  (9 : ℝ) * Sparse.eval nodeValue4090 x + ((12 : ℝ) * Sparse.eval nodeValue4091 x + ((9 : ℝ) * Sparse.eval nodeValue4096 x + 0))

def numericRow993 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 1, -5), (Sum.inr 4090, 360), (Sum.inr 4091, 480)]

theorem reindexCheck993 : Integer.Sparse.reindex keyMap MixedData.row993 = numericRow993 := by decide +kernel

theorem numericCheck993 (x : Master → ℝ) : Integer.Sparse.eval numericRow993 x =
    (40 : ℝ) * reducedSource993 x := by
  norm_num [numericRow993, reducedSource993, Integer.Sparse.eval, Sparse.eval, nodeValue4090, nodeValue4091, nodeValue4096]
  ring

noncomputable def reducedSource994 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue617 x + ((3 : ℝ) * Sparse.eval nodeValue936 x + ((1 : ℝ) * Sparse.eval nodeValue1064 x + ((1 : ℝ) * Sparse.eval nodeValue1091 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))

def numericRow994 : Integer.Sparse Master := [(Sum.inr 617, 1), (Sum.inr 936, 3), (Sum.inr 1064, 1), (Sum.inr 1091, 1), (Sum.inr 4084, -1)]

theorem reindexCheck994 : Integer.Sparse.reindex keyMap MixedData.row994 = numericRow994 := by decide +kernel

theorem numericCheck994 (x : Master → ℝ) : Integer.Sparse.eval numericRow994 x =
    (1 : ℝ) * reducedSource994 x := by
  norm_num [numericRow994, reducedSource994, Integer.Sparse.eval, Sparse.eval, nodeValue617, nodeValue936, nodeValue1064, nodeValue1091, nodeValue4084]

noncomputable def reducedSource995 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue862 x + ((3 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

def numericRow995 : Integer.Sparse Master := [(Sum.inr 862, 1), (Sum.inr 1629, 3), (Sum.inr 1752, 1), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

theorem reindexCheck995 : Integer.Sparse.reindex keyMap MixedData.row995 = numericRow995 := by decide +kernel

theorem numericCheck995 (x : Master → ℝ) : Integer.Sparse.eval numericRow995 x =
    (1 : ℝ) * reducedSource995 x := by
  norm_num [numericRow995, reducedSource995, Integer.Sparse.eval, Sparse.eval, nodeValue862, nodeValue1629, nodeValue1752, nodeValue1757, nodeValue4072]

noncomputable def reducedSource996 (x : Master → ℝ) : ℝ :=
  (3 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue1757 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

def numericRow996 : Integer.Sparse Master := [(Sum.inr 1749, 3), (Sum.inr 1752, 2), (Sum.inr 1757, 1), (Sum.inr 4072, -1)]

theorem reindexCheck996 : Integer.Sparse.reindex keyMap MixedData.row996 = numericRow996 := by decide +kernel

theorem numericCheck996 (x : Master → ℝ) : Integer.Sparse.eval numericRow996 x =
    (1 : ℝ) * reducedSource996 x := by
  norm_num [numericRow996, reducedSource996, Integer.Sparse.eval, Sparse.eval, nodeValue1749, nodeValue1752, nodeValue1757, nodeValue4072]

noncomputable def reducedSource997 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue587 x + ((2 : ℝ) * Sparse.eval nodeValue911 x + ((1 : ℝ) * Sparse.eval nodeValue951 x + ((1 : ℝ) * Sparse.eval nodeValue1027 x + ((1 : ℝ) * Sparse.eval nodeValue1046 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow997 : Integer.Sparse Master := [(Sum.inr 587, 1), (Sum.inr 911, 2), (Sum.inr 951, 1), (Sum.inr 1027, 1), (Sum.inr 1046, 1), (Sum.inr 4083, -1)]

theorem reindexCheck997 : Integer.Sparse.reindex keyMap MixedData.row997 = numericRow997 := by decide +kernel

theorem numericCheck997 (x : Master → ℝ) : Integer.Sparse.eval numericRow997 x =
    (1 : ℝ) * reducedSource997 x := by
  norm_num [numericRow997, reducedSource997, Integer.Sparse.eval, Sparse.eval, nodeValue587, nodeValue911, nodeValue951, nodeValue1027, nodeValue1046, nodeValue4083]

noncomputable def reducedSource998 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue849 x + ((2 : ℝ) * Sparse.eval nodeValue1615 x + ((1 : ℝ) * Sparse.eval nodeValue1749 x + ((2 : ℝ) * Sparse.eval nodeValue1752 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0))))

def numericRow998 : Integer.Sparse Master := [(Sum.inr 849, 1), (Sum.inr 1615, 2), (Sum.inr 1749, 1), (Sum.inr 1752, 2), (Sum.inr 4072, -1)]

theorem reindexCheck998 : Integer.Sparse.reindex keyMap MixedData.row998 = numericRow998 := by decide +kernel

theorem numericCheck998 (x : Master → ℝ) : Integer.Sparse.eval numericRow998 x =
    (1 : ℝ) * reducedSource998 x := by
  norm_num [numericRow998, reducedSource998, Integer.Sparse.eval, Sparse.eval, nodeValue849, nodeValue1615, nodeValue1749, nodeValue1752, nodeValue4072]

noncomputable def reducedSource999 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue794 x + ((1 : ℝ) * Sparse.eval nodeValue797 x + ((1 : ℝ) * Sparse.eval nodeValue813 x + ((1 : ℝ) * Sparse.eval nodeValue828 x + ((1 : ℝ) * Sparse.eval nodeValue1716 x + ((-1 : ℝ) * Sparse.eval nodeValue4069 x + 0)))))

def numericRow999 : Integer.Sparse Master := [(Sum.inr 794, 2), (Sum.inr 797, 1), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 1716, 1), (Sum.inr 4069, -1)]

theorem reindexCheck999 : Integer.Sparse.reindex keyMap MixedData.row999 = numericRow999 := by decide +kernel

theorem numericCheck999 (x : Master → ℝ) : Integer.Sparse.eval numericRow999 x =
    (1 : ℝ) * reducedSource999 x := by
  norm_num [numericRow999, reducedSource999, Integer.Sparse.eval, Sparse.eval, nodeValue794, nodeValue797, nodeValue813, nodeValue828, nodeValue1716, nodeValue4069]

noncomputable def reducedSource1000 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue633 x + ((2 : ℝ) * Sparse.eval nodeValue1115 x + ((1 : ℝ) * Sparse.eval nodeValue1140 x + ((1 : ℝ) * Sparse.eval nodeValue1221 x + ((1 : ℝ) * Sparse.eval nodeValue1242 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1000 : Integer.Sparse Master := [(Sum.inr 633, 1), (Sum.inr 1115, 2), (Sum.inr 1140, 1), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1000 : Integer.Sparse.reindex keyMap MixedData.row1000 = numericRow1000 := by decide +kernel

theorem numericCheck1000 (x : Master → ℝ) : Integer.Sparse.eval numericRow1000 x =
    (1 : ℝ) * reducedSource1000 x := by
  norm_num [numericRow1000, reducedSource1000, Integer.Sparse.eval, Sparse.eval, nodeValue633, nodeValue1115, nodeValue1140, nodeValue1221, nodeValue1242, nodeValue4092]

noncomputable def reducedSource1001 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1615 x + ((1 : ℝ) * Sparse.eval nodeValue1620 x + ((1 : ℝ) * Sparse.eval nodeValue1629 x + ((1 : ℝ) * Sparse.eval nodeValue1752 x + ((1 : ℝ) * Sparse.eval nodeValue3298 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))))

def numericRow1001 : Integer.Sparse Master := [(Sum.inr 1615, 2), (Sum.inr 1620, 1), (Sum.inr 1629, 1), (Sum.inr 1752, 1), (Sum.inr 3298, 1), (Sum.inr 4072, -1)]

theorem reindexCheck1001 : Integer.Sparse.reindex keyMap MixedData.row1001 = numericRow1001 := by decide +kernel

theorem numericCheck1001 (x : Master → ℝ) : Integer.Sparse.eval numericRow1001 x =
    (1 : ℝ) * reducedSource1001 x := by
  norm_num [numericRow1001, reducedSource1001, Integer.Sparse.eval, Sparse.eval, nodeValue1615, nodeValue1620, nodeValue1629, nodeValue1752, nodeValue3298, nodeValue4072]

noncomputable def reducedSource1002 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue1752 x + ((3 : ℝ) * Sparse.eval nodeValue3298 x + ((1 : ℝ) * Sparse.eval nodeValue3313 x + ((-1 : ℝ) * Sparse.eval nodeValue4072 x + 0)))

def numericRow1002 : Integer.Sparse Master := [(Sum.inr 1752, 2), (Sum.inr 3298, 3), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

theorem reindexCheck1002 : Integer.Sparse.reindex keyMap MixedData.row1002 = numericRow1002 := by decide +kernel

theorem numericCheck1002 (x : Master → ℝ) : Integer.Sparse.eval numericRow1002 x =
    (1 : ℝ) * reducedSource1002 x := by
  norm_num [numericRow1002, reducedSource1002, Integer.Sparse.eval, Sparse.eval, nodeValue1752, nodeValue3298, nodeValue3313, nodeValue4072]

noncomputable def reducedSource1003 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue989 x + ((1 : ℝ) * Sparse.eval nodeValue994 x + ((1 : ℝ) * Sparse.eval nodeValue1009 x + ((1 : ℝ) * Sparse.eval nodeValue1055 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1003 : Integer.Sparse Master := [(Sum.inr 989, 2), (Sum.inr 994, 1), (Sum.inr 1009, 1), (Sum.inr 1055, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1003 : Integer.Sparse.reindex keyMap MixedData.row1003 = numericRow1003 := by decide +kernel

theorem numericCheck1003 (x : Master → ℝ) : Integer.Sparse.eval numericRow1003 x =
    (1 : ℝ) * reducedSource1003 x := by
  norm_num [numericRow1003, reducedSource1003, Integer.Sparse.eval, Sparse.eval, nodeValue989, nodeValue994, nodeValue1009, nodeValue1055, nodeValue2218, nodeValue4082]

noncomputable def reducedSource1004 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue994 x + ((2 : ℝ) * Sparse.eval nodeValue1179 x + ((1 : ℝ) * Sparse.eval nodeValue1190 x + ((1 : ℝ) * Sparse.eval nodeValue1258 x + ((1 : ℝ) * Sparse.eval nodeValue2218 x + ((-1 : ℝ) * Sparse.eval nodeValue4082 x + 0)))))

def numericRow1004 : Integer.Sparse Master := [(Sum.inr 994, 1), (Sum.inr 1179, 2), (Sum.inr 1190, 1), (Sum.inr 1258, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem reindexCheck1004 : Integer.Sparse.reindex keyMap MixedData.row1004 = numericRow1004 := by decide +kernel

theorem numericCheck1004 (x : Master → ℝ) : Integer.Sparse.eval numericRow1004 x =
    (1 : ℝ) * reducedSource1004 x := by
  norm_num [numericRow1004, reducedSource1004, Integer.Sparse.eval, Sparse.eval, nodeValue994, nodeValue1179, nodeValue1190, nodeValue1258, nodeValue2218, nodeValue4082]

noncomputable def reducedSource1005 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue971 x + ((1 : ℝ) * Sparse.eval nodeValue975 x + ((2 : ℝ) * Sparse.eval nodeValue982 x + ((1 : ℝ) * Sparse.eval nodeValue1019 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1005 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 982, 2), (Sum.inr 1019, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1005 : Integer.Sparse.reindex keyMap MixedData.row1005 = numericRow1005 := by decide +kernel

theorem numericCheck1005 (x : Master → ℝ) : Integer.Sparse.eval numericRow1005 x =
    (1 : ℝ) * reducedSource1005 x := by
  norm_num [numericRow1005, reducedSource1005, Integer.Sparse.eval, Sparse.eval, nodeValue971, nodeValue975, nodeValue982, nodeValue1019, nodeValue2193, nodeValue4080]

noncomputable def reducedSource1006 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue975 x + ((1 : ℝ) * Sparse.eval nodeValue1194 x + ((1 : ℝ) * Sparse.eval nodeValue1202 x + ((2 : ℝ) * Sparse.eval nodeValue1211 x + ((1 : ℝ) * Sparse.eval nodeValue2193 x + ((-1 : ℝ) * Sparse.eval nodeValue4080 x + 0)))))

def numericRow1006 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 1194, 1), (Sum.inr 1202, 1), (Sum.inr 1211, 2), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem reindexCheck1006 : Integer.Sparse.reindex keyMap MixedData.row1006 = numericRow1006 := by decide +kernel

theorem numericCheck1006 (x : Master → ℝ) : Integer.Sparse.eval numericRow1006 x =
    (1 : ℝ) * reducedSource1006 x := by
  norm_num [numericRow1006, reducedSource1006, Integer.Sparse.eval, Sparse.eval, nodeValue975, nodeValue1194, nodeValue1202, nodeValue1211, nodeValue2193, nodeValue4080]

noncomputable def reducedSource1007 (x : Master → ℝ) : ℝ :=
  (8 : ℝ) * Sparse.eval nodeValue4187 x + ((1 : ℝ) * Sparse.eval nodeValue4194 x + ((12 : ℝ) * Sparse.eval nodeValue4555 x + ((8 : ℝ) * Sparse.eval nodeValue4625 x + ((1 : ℝ) * Sparse.eval nodeValue5312 x + 0))))

def numericRow1007 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 5, -4), (Sum.inl 6, -1), (Sum.inl 1, 4), (Sum.inr 615, -144), (Sum.inr 622, -18), (Sum.inr 1140, -216), (Sum.inr 1537, -144), (Sum.inr 1541, -18), (Sum.inr 3275, -216), (Sum.inr 3310, -144)]

theorem reindexCheck1007 : Integer.Sparse.reindex keyMap MixedData.row1007 = numericRow1007 := by decide +kernel

theorem numericCheck1007 (x : Master → ℝ) : Integer.Sparse.eval numericRow1007 x =
    (72 : ℝ) * reducedSource1007 x := by
  norm_num [numericRow1007, reducedSource1007, Integer.Sparse.eval, Sparse.eval, nodeValue4187, nodeValue4194, nodeValue4555, nodeValue4625, nodeValue5312]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
