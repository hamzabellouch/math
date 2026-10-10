import OAI.Analysis.MutuallyUnbiased.Moments.MomentContraction
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical141
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical248
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def pivotPermutation2304 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2304 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem sound2304 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2304 = Sparse.eval value2304 (momentVector H) := by
  have heq : pivotMatrix2304 = (fun u v => node2304 (pivotPermutation2304 u) v) := by apply Matrix.ext; unfold pivotMatrix2304 node2304 pivotPermutation2304; decide +kernel
  have hmoment : injectiveMoment H node2304 = injectiveMoment H pivotMatrix2304 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2304 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2304 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2304 (0 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2304 (0 : Fin 5) = raw4067 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2304 raw4067; decide +kernel
    rw [heq]
    exact (canonical4067 hH).trans (sound655 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2304 (1 : Fin 5)) =
      Sparse.eval value704 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2304 (1 : Fin 5) = raw4912 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2304 raw4912; decide +kernel
    rw [heq]
    exact (canonical4912 hH).trans (sound704 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2304 (2 : Fin 5)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2304 (2 : Fin 5) = raw4934 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2304 raw4934; decide +kernel
    rw [heq]
    exact (canonical4934 hH).trans (sound227 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2304 (3 : Fin 5)) =
      Sparse.eval value227 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2304 (3 : Fin 5) = raw4937 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2304 raw4937; decide +kernel
    rw [heq]
    exact (canonical4937 hH).trans (sound227 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2304 (4 : Fin 5)) =
      Sparse.eval value655 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2304 (4 : Fin 5) = raw4939 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2304 raw4939; decide +kernel
    rw [heq]
    exact (canonical4939 hH).trans (sound655 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2304 + (injectiveMoment H (mergeFirst pivotMatrix2304 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2304 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2304 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2304 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2304 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2304, value227, value655, value704, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2305 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2305 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem sound2305 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2305 = Sparse.eval value2305 (momentVector H) := by
  have heq : pivotMatrix2305 = (fun u v => node2305 (pivotPermutation2305 u) v) := by apply Matrix.ext; unfold pivotMatrix2305 node2305 pivotPermutation2305; decide +kernel
  have hmoment : injectiveMoment H node2305 = injectiveMoment H pivotMatrix2305 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2305 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2305 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2305 (0 : Fin 5)) =
      Sparse.eval value659 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2305 (0 : Fin 5) = raw4071 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2305 raw4071; decide +kernel
    rw [heq]
    exact (canonical4071 hH).trans (sound659 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2305 (1 : Fin 5)) =
      Sparse.eval value705 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2305 (1 : Fin 5) = raw4913 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2305 raw4913; decide +kernel
    rw [heq]
    exact (canonical4913 hH).trans (sound705 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2305 (2 : Fin 5)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2305 (2 : Fin 5) = raw4935 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2305 raw4935; decide +kernel
    rw [heq]
    exact (canonical4935 hH).trans (sound230 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2305 (3 : Fin 5)) =
      Sparse.eval value710 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2305 (3 : Fin 5) = raw4940 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2305 raw4940; decide +kernel
    rw [heq]
    exact (canonical4940 hH).trans (sound710 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2305 (4 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2305 (4 : Fin 5) = raw4941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2305 raw4941; decide +kernel
    rw [heq]
    exact (canonical4941 hH).trans (sound711 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2305 + (injectiveMoment H (mergeFirst pivotMatrix2305 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2305 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2305 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2305 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2305 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2305, value230, value659, value705, value710, value711, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2306 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2306 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem sound2306 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2306 = Sparse.eval value2306 (momentVector H) := by
  have heq : pivotMatrix2306 = (fun u v => node2306 (pivotPermutation2306 u) v) := by apply Matrix.ext; unfold pivotMatrix2306 node2306 pivotPermutation2306; decide +kernel
  have hmoment : injectiveMoment H node2306 = injectiveMoment H pivotMatrix2306 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2306 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2306 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2306 (0 : Fin 5)) =
      Sparse.eval value1291 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2306 (0 : Fin 5) = raw4072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2306 raw4072; decide +kernel
    rw [heq]
    exact (canonical4072 hH).trans (sound1291 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2306 (1 : Fin 5)) =
      Sparse.eval value667 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2306 (1 : Fin 5) = raw4914 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2306 raw4914; decide +kernel
    rw [heq]
    exact (canonical4914 hH).trans (sound667 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2306 (2 : Fin 5)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2306 (2 : Fin 5) = raw4936 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2306 raw4936; decide +kernel
    rw [heq]
    exact (canonical4936 hH).trans (sound287 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2306 (3 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2306 (3 : Fin 5) = raw4941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2306 raw4941; decide +kernel
    rw [heq]
    exact (canonical4941 hH).trans (sound711 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2306 (4 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2306 (4 : Fin 5) = raw4942 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2306 raw4942; decide +kernel
    rw [heq]
    exact (canonical4942 hH).trans (sound711 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2306 + (injectiveMoment H (mergeFirst pivotMatrix2306 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2306 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2306 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2306 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2306 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2306, value1291, value287, value667, value711, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2307 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2307 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 1, -3]]

theorem sound2307 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2307 = Sparse.eval value2307 (momentVector H) := by
  have heq : pivotMatrix2307 = (fun u v => node2307 (pivotPermutation2307 u) v) := by apply Matrix.ext; unfold pivotMatrix2307 node2307 pivotPermutation2307; decide +kernel
  have hmoment : injectiveMoment H node2307 = injectiveMoment H pivotMatrix2307 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2307 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2307 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2307 (0 : Fin 4)) =
      Sparse.eval value1157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2307 (0 : Fin 4) = raw5058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2307 raw5058; decide +kernel
    rw [heq]
    exact (canonical5058 hH).trans (sound1157 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2307 (1 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2307 (1 : Fin 4) = raw5003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2307 raw5003; decide +kernel
    rw [heq]
    exact (canonical5003 hH).trans (sound1352 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2307 (2 : Fin 4)) =
      Sparse.eval value712 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2307 (2 : Fin 4) = raw4994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2307 raw4994; decide +kernel
    rw [heq]
    exact (canonical4994 hH).trans (sound712 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2307 (3 : Fin 4)) =
      Sparse.eval value1353 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2307 (3 : Fin 4) = raw4993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2307 raw4993; decide +kernel
    rw [heq]
    exact (canonical4993 hH).trans (sound1353 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2307 + (injectiveMoment H (mergeFirst pivotMatrix2307 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2307 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2307 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2307 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2307, value1157, value1352, value1353, value712, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2308 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2308 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 0, -2]]

theorem sound2308 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2308 = Sparse.eval value2308 (momentVector H) := by
  have heq : pivotMatrix2308 = (fun u v => node2308 (pivotPermutation2308 u) v) := by apply Matrix.ext; unfold pivotMatrix2308 node2308 pivotPermutation2308; decide +kernel
  have hmoment : injectiveMoment H node2308 = injectiveMoment H pivotMatrix2308 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2308 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2308 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2308 (0 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2308 (0 : Fin 4) = raw5059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2308 raw5059; decide +kernel
    rw [heq]
    exact (canonical5059 hH).trans (sound467 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2308 (1 : Fin 4)) =
      Sparse.eval value490 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2308 (1 : Fin 4) = raw5004 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2308 raw5004; decide +kernel
    rw [heq]
    exact (canonical5004 hH).trans (sound490 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2308 (2 : Fin 4)) =
      Sparse.eval value583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2308 (2 : Fin 4) = raw4995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2308 raw4995; decide +kernel
    rw [heq]
    exact (canonical4995 hH).trans (sound583 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2308 (3 : Fin 4)) =
      Sparse.eval value712 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2308 (3 : Fin 4) = raw4994 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2308 raw4994; decide +kernel
    rw [heq]
    exact (canonical4994 hH).trans (sound712 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2308 + (injectiveMoment H (mergeFirst pivotMatrix2308 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2308 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2308 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2308 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2308, value467, value490, value583, value712, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2309 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2309 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

theorem sound2309 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2309 = Sparse.eval value2309 (momentVector H) := by
  have heq : pivotMatrix2309 = (fun u v => node2309 (pivotPermutation2309 u) v) := by apply Matrix.ext; unfold pivotMatrix2309 node2309 pivotPermutation2309; decide +kernel
  have hmoment : injectiveMoment H node2309 = injectiveMoment H pivotMatrix2309 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2309 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2309 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2309 (0 : Fin 4)) =
      Sparse.eval value1031 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2309 (0 : Fin 4) = raw7484 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2309 raw7484; decide +kernel
    rw [heq]
    exact (canonical7484 hH).trans (sound1031 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2309 (1 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2309 (1 : Fin 4) = raw5045 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2309 raw5045; decide +kernel
    rw [heq]
    exact (canonical5045 hH).trans (sound400 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2309 (2 : Fin 4)) =
      Sparse.eval value583 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2309 (2 : Fin 4) = raw4995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2309 raw4995; decide +kernel
    rw [heq]
    exact (canonical4995 hH).trans (sound583 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2309 (3 : Fin 4)) =
      Sparse.eval value1180 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2309 (3 : Fin 4) = raw4987 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2309 raw4987; decide +kernel
    rw [heq]
    exact (canonical4987 hH).trans (sound1180 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2309 + (injectiveMoment H (mergeFirst pivotMatrix2309 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2309 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2309 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2309 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2309, value1031, value1180, value400, value583, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2310 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2310 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem sound2310 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2310 = Sparse.eval value2310 (momentVector H) := by
  have heq : pivotMatrix2310 = (fun u v => node2310 (pivotPermutation2310 u) v) := by apply Matrix.ext; unfold pivotMatrix2310 node2310 pivotPermutation2310; decide +kernel
  have hmoment : injectiveMoment H node2310 = injectiveMoment H pivotMatrix2310 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2310 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2310 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2310 (0 : Fin 4)) =
      Sparse.eval value1168 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2310 (0 : Fin 4) = raw7485 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2310 raw7485; decide +kernel
    rw [heq]
    exact (canonical7485 hH).trans (sound1168 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2310 (1 : Fin 4)) =
      Sparse.eval value402 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2310 (1 : Fin 4) = raw5046 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2310 raw5046; decide +kernel
    rw [heq]
    exact (canonical5046 hH).trans (sound402 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2310 (2 : Fin 4)) =
      Sparse.eval value1186 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2310 (2 : Fin 4) = raw4996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2310 raw4996; decide +kernel
    rw [heq]
    exact (canonical4996 hH).trans (sound1186 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2310 (3 : Fin 4)) =
      Sparse.eval value578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2310 (3 : Fin 4) = raw4990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2310 raw4990; decide +kernel
    rw [heq]
    exact (canonical4990 hH).trans (sound578 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2310 + (injectiveMoment H (mergeFirst pivotMatrix2310 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2310 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2310 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2310 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2310, value1168, value1186, value402, value578, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2311 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2311 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem sound2311 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2311 = Sparse.eval value2311 (momentVector H) := by
  have heq : pivotMatrix2311 = (fun u v => node2311 (pivotPermutation2311 u) v) := by apply Matrix.ext; unfold pivotMatrix2311 node2311 pivotPermutation2311; decide +kernel
  have hmoment : injectiveMoment H node2311 = injectiveMoment H pivotMatrix2311 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2311 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2311 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2311 (0 : Fin 4)) =
      Sparse.eval value1341 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2311 (0 : Fin 4) = raw7924 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2311 raw7924; decide +kernel
    rw [heq]
    exact (canonical7924 hH).trans (sound1341 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2311 (1 : Fin 4)) =
      Sparse.eval value487 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2311 (1 : Fin 4) = raw5050 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2311 raw5050; decide +kernel
    rw [heq]
    exact (canonical5050 hH).trans (sound487 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2311 (2 : Fin 4)) =
      Sparse.eval value712 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2311 (2 : Fin 4) = raw4998 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2311 raw4998; decide +kernel
    rw [heq]
    exact (canonical4998 hH).trans (sound712 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2311 (3 : Fin 4)) =
      Sparse.eval value578 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2311 (3 : Fin 4) = raw4990 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2311 raw4990; decide +kernel
    rw [heq]
    exact (canonical4990 hH).trans (sound578 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2311 + (injectiveMoment H (mergeFirst pivotMatrix2311 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2311 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2311 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2311 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2311, value1341, value487, value578, value712, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2312 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2312 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem sound2312 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2312 = Sparse.eval value2312 (momentVector H) := by
  have heq : pivotMatrix2312 = (fun u v => node2312 (pivotPermutation2312 u) v) := by apply Matrix.ext; unfold pivotMatrix2312 node2312 pivotPermutation2312; decide +kernel
  have hmoment : injectiveMoment H node2312 = injectiveMoment H pivotMatrix2312 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2312 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2312 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2312 (0 : Fin 4)) =
      Sparse.eval value1167 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2312 (0 : Fin 4) = raw7486 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2312 raw7486; decide +kernel
    rw [heq]
    exact (canonical7486 hH).trans (sound1167 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2312 (1 : Fin 4)) =
      Sparse.eval value1187 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2312 (1 : Fin 4) = raw5047 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2312 raw5047; decide +kernel
    rw [heq]
    exact (canonical5047 hH).trans (sound1187 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2312 (2 : Fin 4)) =
      Sparse.eval value1185 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2312 (2 : Fin 4) = raw4997 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2312 raw4997; decide +kernel
    rw [heq]
    exact (canonical4997 hH).trans (sound1185 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2312 (3 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2312 (3 : Fin 4) = raw4992 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2312 raw4992; decide +kernel
    rw [heq]
    exact (canonical4992 hH).trans (sound688 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2312 + (injectiveMoment H (mergeFirst pivotMatrix2312 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2312 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2312 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2312 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2312, value1167, value1185, value1187, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2313 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2313 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![1, -1, 0, 0], ![1, 1, 2, -4]]

theorem sound2313 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2313 = Sparse.eval value2313 (momentVector H) := by
  have heq : pivotMatrix2313 = (fun u v => node2313 (pivotPermutation2313 u) v) := by apply Matrix.ext; unfold pivotMatrix2313 node2313 pivotPermutation2313; decide +kernel
  have hmoment : injectiveMoment H node2313 = injectiveMoment H pivotMatrix2313 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2313 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2313 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2313 (0 : Fin 4)) =
      Sparse.eval value1348 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2313 (0 : Fin 4) = raw4655 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2313 raw4655; decide +kernel
    rw [heq]
    exact (canonical4655 hH).trans (sound1348 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2313 (1 : Fin 4)) =
      Sparse.eval value1353 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2313 (1 : Fin 4) = raw4993 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2313 raw4993; decide +kernel
    rw [heq]
    exact (canonical4993 hH).trans (sound1353 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2313 (2 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2313 (2 : Fin 4) = raw5002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2313 raw5002; decide +kernel
    rw [heq]
    exact (canonical5002 hH).trans (sound693 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2313 (3 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2313 (3 : Fin 4) = raw5003 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2313 raw5003; decide +kernel
    rw [heq]
    exact (canonical5003 hH).trans (sound1352 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2313 + (injectiveMoment H (mergeFirst pivotMatrix2313 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2313 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2313 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2313 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2313, value1348, value1352, value1353, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2314 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2314 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, -1, 0], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

theorem sound2314 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2314 = Sparse.eval value2314 (momentVector H) := by
  have heq : pivotMatrix2314 = (fun u v => node2314 (pivotPermutation2314 u) v) := by apply Matrix.ext; unfold pivotMatrix2314 node2314 pivotPermutation2314; decide +kernel
  have hmoment : injectiveMoment H node2314 = injectiveMoment H pivotMatrix2314 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2314 0 = Pi.single (0 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2314 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2314 (0 : Fin 4)) =
      Sparse.eval value787 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2314 (0 : Fin 4) = raw7897 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2314 raw7897; decide +kernel
    rw [heq]
    exact (canonical7897 hH).trans (sound787 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2314 (1 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2314 (1 : Fin 4) = raw5051 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2314 raw5051; decide +kernel
    rw [heq]
    exact (canonical5051 hH).trans (sound585 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2314 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2314 (2 : Fin 4) = raw5012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2314 raw5012; decide +kernel
    rw [heq]
    exact (canonical5012 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2314 (3 : Fin 4)) =
      Sparse.eval value398 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2314 (3 : Fin 4) = raw5006 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2314 raw5006; decide +kernel
    rw [heq]
    exact (canonical5006 hH).trans (sound398 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2314 + (injectiveMoment H (mergeFirst pivotMatrix2314 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2314 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2314 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2314 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2314, value398, value585, value787, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2315 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2315 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem sound2315 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2315 = Sparse.eval value2315 (momentVector H) := by
  have heq : pivotMatrix2315 = (fun u v => node2315 (pivotPermutation2315 u) v) := by apply Matrix.ext; unfold pivotMatrix2315 node2315 pivotPermutation2315; decide +kernel
  have hmoment : injectiveMoment H node2315 = injectiveMoment H pivotMatrix2315 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2315 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2315 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2315 (0 : Fin 4)) =
      Sparse.eval value939 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2315 (0 : Fin 4) = raw3694 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2315 raw3694; decide +kernel
    rw [heq]
    exact (canonical3694 hH).trans (sound939 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2315 (1 : Fin 4)) =
      Sparse.eval value1352 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2315 (1 : Fin 4) = raw4979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2315 raw4979; decide +kernel
    rw [heq]
    exact (canonical4979 hH).trans (sound1352 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2315 (2 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2315 (2 : Fin 4) = raw5013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2315 raw5013; decide +kernel
    rw [heq]
    exact (canonical5013 hH).trans (sound477 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2315 (3 : Fin 4)) =
      Sparse.eval value1000 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2315 (3 : Fin 4) = raw5014 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2315 raw5014; decide +kernel
    rw [heq]
    exact (canonical5014 hH).trans (sound1000 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2315 + (injectiveMoment H (mergeFirst pivotMatrix2315 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2315 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2315 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2315 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2315, value1000, value1352, value477, value939, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2316 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2316 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

theorem sound2316 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2316 = Sparse.eval value2316 (momentVector H) := by
  have heq : pivotMatrix2316 = (fun u v => node2316 (pivotPermutation2316 u) v) := by apply Matrix.ext; unfold pivotMatrix2316 node2316 pivotPermutation2316; decide +kernel
  have hmoment : injectiveMoment H node2316 = injectiveMoment H pivotMatrix2316 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2316 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2316 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2316 (0 : Fin 4)) =
      Sparse.eval value914 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2316 (0 : Fin 4) = raw7488 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2316 raw7488; decide +kernel
    rw [heq]
    exact (canonical7488 hH).trans (sound914 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2316 (1 : Fin 4)) =
      Sparse.eval value579 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2316 (1 : Fin 4) = raw5048 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2316 raw5048; decide +kernel
    rw [heq]
    exact (canonical5048 hH).trans (sound579 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2316 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2316 (2 : Fin 4) = raw5012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2316 raw5012; decide +kernel
    rw [heq]
    exact (canonical5012 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2316 (3 : Fin 4)) =
      Sparse.eval value1257 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2316 (3 : Fin 4) = raw5008 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2316 raw5008; decide +kernel
    rw [heq]
    exact (canonical5008 hH).trans (sound1257 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2316 + (injectiveMoment H (mergeFirst pivotMatrix2316 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2316 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2316 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2316 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2316, value1257, value579, value585, value914, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2317 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2317 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

theorem sound2317 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2317 = Sparse.eval value2317 (momentVector H) := by
  have heq : pivotMatrix2317 = (fun u v => node2317 (pivotPermutation2317 u) v) := by apply Matrix.ext; unfold pivotMatrix2317 node2317 pivotPermutation2317; decide +kernel
  have hmoment : injectiveMoment H node2317 = injectiveMoment H pivotMatrix2317 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2317 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2317 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2317 (0 : Fin 4)) =
      Sparse.eval value454 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (0 : Fin 4) = raw4674 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw4674; decide +kernel
    rw [heq]
    exact (canonical4674 hH).trans (sound454 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2317 (1 : Fin 4)) =
      Sparse.eval value693 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (1 : Fin 4) = raw5002 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5002; decide +kernel
    rw [heq]
    exact (canonical5002 hH).trans (sound693 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2317 (2 : Fin 4)) =
      Sparse.eval value585 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (2 : Fin 4) = raw5012 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5012; decide +kernel
    rw [heq]
    exact (canonical5012 hH).trans (sound585 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2317 (3 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2317 (3 : Fin 4) = raw5013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2317 raw5013; decide +kernel
    rw [heq]
    exact (canonical5013 hH).trans (sound477 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2317 + (injectiveMoment H (mergeFirst pivotMatrix2317 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2317 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2317, value454, value477, value585, value693, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2318 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2318 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

theorem sound2318 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2318 = Sparse.eval value2318 (momentVector H) := by
  have heq : pivotMatrix2318 = (fun u v => node2318 (pivotPermutation2318 u) v) := by apply Matrix.ext; unfold pivotMatrix2318 node2318 pivotPermutation2318; decide +kernel
  have hmoment : injectiveMoment H node2318 = injectiveMoment H pivotMatrix2318 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2318 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2318 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2318 (0 : Fin 4)) =
      Sparse.eval value942 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2318 (0 : Fin 4) = raw3759 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2318 raw3759; decide +kernel
    rw [heq]
    exact (canonical3759 hH).trans (sound942 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2318 (1 : Fin 4)) =
      Sparse.eval value477 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2318 (1 : Fin 4) = raw5013 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2318 raw5013; decide +kernel
    rw [heq]
    exact (canonical5013 hH).trans (sound477 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2318 (2 : Fin 4)) =
      Sparse.eval value1208 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2318 (2 : Fin 4) = raw5026 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2318 raw5026; decide +kernel
    rw [heq]
    exact (canonical5026 hH).trans (sound1208 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2318 (3 : Fin 4)) =
      Sparse.eval value1006 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2318 (3 : Fin 4) = raw5027 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2318 raw5027; decide +kernel
    rw [heq]
    exact (canonical5027 hH).trans (sound1006 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2318 + (injectiveMoment H (mergeFirst pivotMatrix2318 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2318 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2318 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2318 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2318, value1006, value1208, value477, value942, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2319 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2319 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

theorem sound2319 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2319 = Sparse.eval value2319 (momentVector H) := by
  have heq : pivotMatrix2319 = (fun u v => node2319 (pivotPermutation2319 u) v) := by apply Matrix.ext; unfold pivotMatrix2319 node2319 pivotPermutation2319; decide +kernel
  have hmoment : injectiveMoment H node2319 = injectiveMoment H pivotMatrix2319 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2319 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2319 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2319 (0 : Fin 4)) =
      Sparse.eval value965 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (0 : Fin 4) = raw3777 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw3777; decide +kernel
    rw [heq]
    exact (canonical3777 hH).trans (sound965 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2319 (1 : Fin 4)) =
      Sparse.eval value980 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (1 : Fin 4) = raw5018 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5018; decide +kernel
    rw [heq]
    exact (canonical5018 hH).trans (sound980 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2319 (2 : Fin 4)) =
      Sparse.eval value932 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (2 : Fin 4) = raw5032 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5032; decide +kernel
    rw [heq]
    exact (canonical5032 hH).trans (sound932 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2319 (3 : Fin 4)) =
      Sparse.eval value800 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2319 (3 : Fin 4) = raw5033 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2319 raw5033; decide +kernel
    rw [heq]
    exact (canonical5033 hH).trans (sound800 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2319 + (injectiveMoment H (mergeFirst pivotMatrix2319 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2319 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2319, value800, value932, value965, value980, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2320 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2320 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem sound2320 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2320 = Sparse.eval value2320 (momentVector H) := by
  have heq : pivotMatrix2320 = (fun u v => node2320 (pivotPermutation2320 u) v) := by apply Matrix.ext; unfold pivotMatrix2320 node2320 pivotPermutation2320; decide +kernel
  have hmoment : injectiveMoment H node2320 = injectiveMoment H pivotMatrix2320 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2320 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2320 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2320 (0 : Fin 4)) =
      Sparse.eval value1035 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2320 (0 : Fin 4) = raw3783 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2320 raw3783; decide +kernel
    rw [heq]
    exact (canonical3783 hH).trans (sound1035 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2320 (1 : Fin 4)) =
      Sparse.eval value495 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2320 (1 : Fin 4) = raw5019 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2320 raw5019; decide +kernel
    rw [heq]
    exact (canonical5019 hH).trans (sound495 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2320 (2 : Fin 4)) =
      Sparse.eval value400 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2320 (2 : Fin 4) = raw5037 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2320 raw5037; decide +kernel
    rw [heq]
    exact (canonical5037 hH).trans (sound400 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2320 (3 : Fin 4)) =
      Sparse.eval value803 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2320 (3 : Fin 4) = raw5038 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2320 raw5038; decide +kernel
    rw [heq]
    exact (canonical5038 hH).trans (sound803 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2320 + (injectiveMoment H (mergeFirst pivotMatrix2320 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2320 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2320 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2320 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2320, value1035, value400, value495, value803, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2321 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2321 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 1, 2, -1], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem sound2321 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2321 = Sparse.eval value2321 (momentVector H) := by
  have heq : pivotMatrix2321 = (fun u v => node2321 (pivotPermutation2321 u) v) := by apply Matrix.ext; unfold pivotMatrix2321 node2321 pivotPermutation2321; decide +kernel
  have hmoment : injectiveMoment H node2321 = injectiveMoment H pivotMatrix2321 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2321 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2321 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2321 (0 : Fin 4)) =
      Sparse.eval value1064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2321 (0 : Fin 4) = raw5077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2321 raw5077; decide +kernel
    rw [heq]
    exact (canonical5077 hH).trans (sound1064 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2321 (1 : Fin 4)) =
      Sparse.eval value1056 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2321 (1 : Fin 4) = raw5062 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2321 raw5062; decide +kernel
    rw [heq]
    exact (canonical5062 hH).trans (sound1056 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2321 (2 : Fin 4)) =
      Sparse.eval value467 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2321 (2 : Fin 4) = raw5059 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2321 raw5059; decide +kernel
    rw [heq]
    exact (canonical5059 hH).trans (sound467 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2321 (3 : Fin 4)) =
      Sparse.eval value1157 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2321 (3 : Fin 4) = raw5058 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2321 raw5058; decide +kernel
    rw [heq]
    exact (canonical5058 hH).trans (sound1157 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2321 + (injectiveMoment H (mergeFirst pivotMatrix2321 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2321 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2321 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2321 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2321, value1056, value1064, value1157, value467, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2322 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2322 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem sound2322 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2322 = Sparse.eval value2322 (momentVector H) := by
  have heq : pivotMatrix2322 = (fun u v => node2322 (pivotPermutation2322 u) v) := by apply Matrix.ext; unfold pivotMatrix2322 node2322 pivotPermutation2322; decide +kernel
  have hmoment : injectiveMoment H node2322 = injectiveMoment H pivotMatrix2322 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2322 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2322 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2322 (0 : Fin 4)) =
      Sparse.eval value1170 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2322 (0 : Fin 4) = raw7558 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2322 raw7558; decide +kernel
    rw [heq]
    exact (canonical7558 hH).trans (sound1170 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2322 (1 : Fin 4)) =
      Sparse.eval value788 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2322 (1 : Fin 4) = raw5072 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2322 raw5072; decide +kernel
    rw [heq]
    exact (canonical5072 hH).trans (sound788 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2322 (2 : Fin 4)) =
      Sparse.eval value767 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2322 (2 : Fin 4) = raw5060 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2322 raw5060; decide +kernel
    rw [heq]
    exact (canonical5060 hH).trans (sound767 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2322 (3 : Fin 4)) =
      Sparse.eval value468 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2322 (3 : Fin 4) = raw5057 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2322 raw5057; decide +kernel
    rw [heq]
    exact (canonical5057 hH).trans (sound468 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2322 + (injectiveMoment H (mergeFirst pivotMatrix2322 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2322 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2322 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2322 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2322, value1170, value468, value767, value788, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2323 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2323 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

theorem sound2323 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2323 = Sparse.eval value2323 (momentVector H) := by
  have heq : pivotMatrix2323 = (fun u v => node2323 (pivotPermutation2323 u) v) := by apply Matrix.ext; unfold pivotMatrix2323 node2323 pivotPermutation2323; decide +kernel
  have hmoment : injectiveMoment H node2323 = injectiveMoment H pivotMatrix2323 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2323 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2323 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2323 (0 : Fin 4)) =
      Sparse.eval value799 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2323 (0 : Fin 4) = raw4192 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2323 raw4192; decide +kernel
    rw [heq]
    exact (canonical4192 hH).trans (sound799 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2323 (1 : Fin 4)) =
      Sparse.eval value1209 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2323 (1 : Fin 4) = raw5064 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2323 raw5064; decide +kernel
    rw [heq]
    exact (canonical5064 hH).trans (sound1209 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2323 (2 : Fin 4)) =
      Sparse.eval value784 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2323 (2 : Fin 4) = raw5065 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2323 raw5065; decide +kernel
    rw [heq]
    exact (canonical5065 hH).trans (sound784 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2323 (3 : Fin 4)) =
      Sparse.eval value968 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2323 (3 : Fin 4) = raw5066 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2323 raw5066; decide +kernel
    rw [heq]
    exact (canonical5066 hH).trans (sound968 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2323 + (injectiveMoment H (mergeFirst pivotMatrix2323 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2323 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2323 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2323 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2323, value1209, value784, value799, value968, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2324 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2324 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem sound2324 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2324 = Sparse.eval value2324 (momentVector H) := by
  have heq : pivotMatrix2324 = (fun u v => node2324 (pivotPermutation2324 u) v) := by apply Matrix.ext; unfold pivotMatrix2324 node2324 pivotPermutation2324; decide +kernel
  have hmoment : injectiveMoment H node2324 = injectiveMoment H pivotMatrix2324 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2324 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2324 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2324 (0 : Fin 4)) =
      Sparse.eval value1061 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2324 (0 : Fin 4) = raw5454 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2324 raw5454; decide +kernel
    rw [heq]
    exact (canonical5454 hH).trans (sound1061 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2324 (1 : Fin 4)) =
      Sparse.eval value1062 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2324 (1 : Fin 4) = raw5093 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2324 raw5093; decide +kernel
    rw [heq]
    exact (canonical5093 hH).trans (sound1062 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2324 (2 : Fin 4)) =
      Sparse.eval value908 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2324 (2 : Fin 4) = raw5078 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2324 raw5078; decide +kernel
    rw [heq]
    exact (canonical5078 hH).trans (sound908 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2324 (3 : Fin 4)) =
      Sparse.eval value1064 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2324 (3 : Fin 4) = raw5077 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2324 raw5077; decide +kernel
    rw [heq]
    exact (canonical5077 hH).trans (sound1064 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2324 + (injectiveMoment H (mergeFirst pivotMatrix2324 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2324 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2324 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2324 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2324, value1061, value1062, value1064, value908, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2325 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2325 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem sound2325 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2325 = Sparse.eval value2325 (momentVector H) := by
  have heq : pivotMatrix2325 = (fun u v => node2325 (pivotPermutation2325 u) v) := by apply Matrix.ext; unfold pivotMatrix2325 node2325 pivotPermutation2325; decide +kernel
  have hmoment : injectiveMoment H node2325 = injectiveMoment H pivotMatrix2325 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2325 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2325 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2325 (0 : Fin 4)) =
      Sparse.eval value1085 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2325 (0 : Fin 4) = raw5455 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2325 raw5455; decide +kernel
    rw [heq]
    exact (canonical5455 hH).trans (sound1085 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2325 (1 : Fin 4)) =
      Sparse.eval value1083 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2325 (1 : Fin 4) = raw5096 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2325 raw5096; decide +kernel
    rw [heq]
    exact (canonical5096 hH).trans (sound1083 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2325 (2 : Fin 4)) =
      Sparse.eval value1046 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2325 (2 : Fin 4) = raw5083 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2325 raw5083; decide +kernel
    rw [heq]
    exact (canonical5083 hH).trans (sound1046 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2325 (3 : Fin 4)) =
      Sparse.eval value713 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2325 (3 : Fin 4) = raw5082 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2325 raw5082; decide +kernel
    rw [heq]
    exact (canonical5082 hH).trans (sound713 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2325 + (injectiveMoment H (mergeFirst pivotMatrix2325 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2325 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2325 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2325 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2325, value1046, value1083, value1085, value713, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2326 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2326 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2]]

theorem sound2326 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2326 = Sparse.eval value2326 (momentVector H) := by
  have heq : pivotMatrix2326 = (fun u v => node2326 (pivotPermutation2326 u) v) := by apply Matrix.ext; unfold pivotMatrix2326 node2326 pivotPermutation2326; decide +kernel
  have hmoment : injectiveMoment H node2326 = injectiveMoment H pivotMatrix2326 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2326 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2326 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2326 (0 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2326 (0 : Fin 4) = raw7614 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2326 raw7614; decide +kernel
    rw [heq]
    exact (canonical7614 hH).trans (sound1052 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2326 (1 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2326 (1 : Fin 4) = raw5100 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2326 raw5100; decide +kernel
    rw [heq]
    exact (canonical5100 hH).trans (sound593 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2326 (2 : Fin 4)) =
      Sparse.eval value714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2326 (2 : Fin 4) = raw5091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2326 raw5091; decide +kernel
    rw [heq]
    exact (canonical5091 hH).trans (sound714 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2326 (3 : Fin 4)) =
      Sparse.eval value1255 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2326 (3 : Fin 4) = raw5086 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2326 raw5086; decide +kernel
    rw [heq]
    exact (canonical5086 hH).trans (sound1255 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2326 + (injectiveMoment H (mergeFirst pivotMatrix2326 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2326 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2326 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2326 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2326, value1052, value1255, value593, value714, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2327 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2327 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 1, 0, -1], ![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem sound2327 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2327 = Sparse.eval value2327 (momentVector H) := by
  have heq : pivotMatrix2327 = (fun u v => node2327 (pivotPermutation2327 u) v) := by apply Matrix.ext; unfold pivotMatrix2327 node2327 pivotPermutation2327; decide +kernel
  have hmoment : injectiveMoment H node2327 = injectiveMoment H pivotMatrix2327 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2327 0 = Pi.single (1 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2327 1 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2327 (0 : Fin 4)) =
      Sparse.eval value1279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2327 (0 : Fin 4) = raw5457 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2327 raw5457; decide +kernel
    rw [heq]
    exact (canonical5457 hH).trans (sound1279 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2327 (1 : Fin 4)) =
      Sparse.eval value1216 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2327 (1 : Fin 4) = raw5098 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2327 raw5098; decide +kernel
    rw [heq]
    exact (canonical5098 hH).trans (sound1216 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2327 (2 : Fin 4)) =
      Sparse.eval value1050 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2327 (2 : Fin 4) = raw5092 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2327 raw5092; decide +kernel
    rw [heq]
    exact (canonical5092 hH).trans (sound1050 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2327 (3 : Fin 4)) =
      Sparse.eval value714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2327 (3 : Fin 4) = raw5091 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2327 raw5091; decide +kernel
    rw [heq]
    exact (canonical5091 hH).trans (sound714 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2327 + (injectiveMoment H (mergeFirst pivotMatrix2327 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2327 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2327 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2327 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2327, value1050, value1216, value1279, value714, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2328 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2328 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound2328 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2328 = Sparse.eval value2328 (momentVector H) := by
  have heq : pivotMatrix2328 = (fun u v => node2328 (pivotPermutation2328 u) v) := by apply Matrix.ext; unfold pivotMatrix2328 node2328 pivotPermutation2328; decide +kernel
  have hmoment : injectiveMoment H node2328 = injectiveMoment H pivotMatrix2328 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2328 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2328 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2328 (0 : Fin 4)) =
      Sparse.eval value994 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2328 (0 : Fin 4) = raw4272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2328 raw4272; decide +kernel
    rw [heq]
    exact (canonical4272 hH).trans (sound994 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2328 (1 : Fin 4)) =
      Sparse.eval value993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2328 (1 : Fin 4) = raw5219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2328 raw5219; decide +kernel
    rw [heq]
    exact (canonical5219 hH).trans (sound993 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2328 (2 : Fin 4)) =
      Sparse.eval value405 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2328 (2 : Fin 4) = raw5228 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2328 raw5228; decide +kernel
    rw [heq]
    exact (canonical5228 hH).trans (sound405 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2328 (3 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2328 (3 : Fin 4) = raw5230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2328 raw5230; decide +kernel
    rw [heq]
    exact (canonical5230 hH).trans (sound991 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2328 + (injectiveMoment H (mergeFirst pivotMatrix2328 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2328 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2328 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2328 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2328, value405, value991, value993, value994, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2329 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2329 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound2329 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2329 = Sparse.eval value2329 (momentVector H) := by
  have heq : pivotMatrix2329 = (fun u v => node2329 (pivotPermutation2329 u) v) := by apply Matrix.ext; unfold pivotMatrix2329 node2329 pivotPermutation2329; decide +kernel
  have hmoment : injectiveMoment H node2329 = injectiveMoment H pivotMatrix2329 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2329 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2329 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2329 (0 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2329 (0 : Fin 4) = raw5294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2329 raw5294; decide +kernel
    rw [heq]
    exact (canonical5294 hH).trans (sound1237 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2329 (1 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2329 (1 : Fin 4) = raw5230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2329 raw5230; decide +kernel
    rw [heq]
    exact (canonical5230 hH).trans (sound991 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2329 (2 : Fin 4)) =
      Sparse.eval value930 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2329 (2 : Fin 4) = raw5227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2329 raw5227; decide +kernel
    rw [heq]
    exact (canonical5227 hH).trans (sound930 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2329 (3 : Fin 4)) =
      Sparse.eval value1195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2329 (3 : Fin 4) = raw5226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2329 raw5226; decide +kernel
    rw [heq]
    exact (canonical5226 hH).trans (sound1195 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2329 + (injectiveMoment H (mergeFirst pivotMatrix2329 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2329 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2329 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2329 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2329, value1195, value1237, value930, value991, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2330 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2330 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -3, 3], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem sound2330 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2330 = Sparse.eval value2330 (momentVector H) := by
  have heq : pivotMatrix2330 = (fun u v => node2330 (pivotPermutation2330 u) v) := by apply Matrix.ext; unfold pivotMatrix2330 node2330 pivotPermutation2330; decide +kernel
  have hmoment : injectiveMoment H node2330 = injectiveMoment H pivotMatrix2330 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2330 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2330 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2330 (0 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2330 (0 : Fin 4) = raw5299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2330 raw5299; decide +kernel
    rw [heq]
    exact (canonical5299 hH).trans (sound1027 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2330 (1 : Fin 4)) =
      Sparse.eval value1021 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2330 (1 : Fin 4) = raw5232 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2330 raw5232; decide +kernel
    rw [heq]
    exact (canonical5232 hH).trans (sound1021 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2330 (2 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2330 (2 : Fin 4) = raw5231 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2330 raw5231; decide +kernel
    rw [heq]
    exact (canonical5231 hH).trans (sound991 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2330 (3 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2330 (3 : Fin 4) = raw5230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2330 raw5230; decide +kernel
    rw [heq]
    exact (canonical5230 hH).trans (sound991 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2330 + (injectiveMoment H (mergeFirst pivotMatrix2330 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2330 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2330 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2330 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2330, value1021, value1027, value991, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2331 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2331 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2]]

theorem sound2331 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2331 = Sparse.eval value2331 (momentVector H) := by
  have heq : pivotMatrix2331 = (fun u v => node2331 (pivotPermutation2331 u) v) := by apply Matrix.ext; unfold pivotMatrix2331 node2331 pivotPermutation2331; decide +kernel
  have hmoment : injectiveMoment H node2331 = injectiveMoment H pivotMatrix2331 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2331 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2331 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2331 (0 : Fin 4)) =
      Sparse.eval value1276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2331 (0 : Fin 4) = raw7959 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2331 raw7959; decide +kernel
    rw [heq]
    exact (canonical7959 hH).trans (sound1276 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2331 (1 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2331 (1 : Fin 4) = raw5303 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2331 raw5303; decide +kernel
    rw [heq]
    exact (canonical5303 hH).trans (sound500 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2331 (2 : Fin 4)) =
      Sparse.eval value718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2331 (2 : Fin 4) = raw5245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2331 raw5245; decide +kernel
    rw [heq]
    exact (canonical5245 hH).trans (sound718 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2331 (3 : Fin 4)) =
      Sparse.eval value593 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2331 (3 : Fin 4) = raw5236 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2331 raw5236; decide +kernel
    rw [heq]
    exact (canonical5236 hH).trans (sound593 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2331 + (injectiveMoment H (mergeFirst pivotMatrix2331 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2331 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2331 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2331 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2331, value1276, value500, value593, value718, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2332 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2332 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1]]

theorem sound2332 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2332 = Sparse.eval value2332 (momentVector H) := by
  have heq : pivotMatrix2332 = (fun u v => node2332 (pivotPermutation2332 u) v) := by apply Matrix.ext; unfold pivotMatrix2332 node2332 pivotPermutation2332; decide +kernel
  have hmoment : injectiveMoment H node2332 = injectiveMoment H pivotMatrix2332 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2332 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2332 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2332 (0 : Fin 4)) =
      Sparse.eval value1286 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2332 (0 : Fin 4) = raw7960 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2332 raw7960; decide +kernel
    rw [heq]
    exact (canonical7960 hH).trans (sound1286 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2332 (1 : Fin 4)) =
      Sparse.eval value1073 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2332 (1 : Fin 4) = raw5304 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2332 raw5304; decide +kernel
    rw [heq]
    exact (canonical5304 hH).trans (sound1073 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2332 (2 : Fin 4)) =
      Sparse.eval value1274 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2332 (2 : Fin 4) = raw5246 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2332 raw5246; decide +kernel
    rw [heq]
    exact (canonical5246 hH).trans (sound1274 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2332 (3 : Fin 4)) =
      Sparse.eval value610 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2332 (3 : Fin 4) = raw5238 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2332 raw5238; decide +kernel
    rw [heq]
    exact (canonical5238 hH).trans (sound610 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2332 + (injectiveMoment H (mergeFirst pivotMatrix2332 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2332 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2332 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2332 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2332, value1073, value1274, value1286, value610, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2333 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2333 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound2333 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2333 = Sparse.eval value2333 (momentVector H) := by
  have heq : pivotMatrix2333 = (fun u v => node2333 (pivotPermutation2333 u) v) := by apply Matrix.ext; unfold pivotMatrix2333 node2333 pivotPermutation2333; decide +kernel
  have hmoment : injectiveMoment H node2333 = injectiveMoment H pivotMatrix2333 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2333 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2333 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2333 (0 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2333 (0 : Fin 4) = raw5309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2333 raw5309; decide +kernel
    rw [heq]
    exact (canonical5309 hH).trans (sound1007 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2333 (1 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2333 (1 : Fin 4) = raw5249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2333 raw5249; decide +kernel
    rw [heq]
    exact (canonical5249 hH).trans (sound1052 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2333 (2 : Fin 4)) =
      Sparse.eval value714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2333 (2 : Fin 4) = raw5244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2333 raw5244; decide +kernel
    rw [heq]
    exact (canonical5244 hH).trans (sound714 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2333 (3 : Fin 4)) =
      Sparse.eval value1014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2333 (3 : Fin 4) = raw5243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2333 raw5243; decide +kernel
    rw [heq]
    exact (canonical5243 hH).trans (sound1014 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2333 + (injectiveMoment H (mergeFirst pivotMatrix2333 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2333 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2333 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2333 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2333, value1007, value1014, value1052, value714, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2334 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2334 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound2334 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2334 = Sparse.eval value2334 (momentVector H) := by
  have heq : pivotMatrix2334 = (fun u v => node2334 (pivotPermutation2334 u) v) := by apply Matrix.ext; unfold pivotMatrix2334 node2334 pivotPermutation2334; decide +kernel
  have hmoment : injectiveMoment H node2334 = injectiveMoment H pivotMatrix2334 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2334 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2334 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2334 (0 : Fin 4)) =
      Sparse.eval value522 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2334 (0 : Fin 4) = raw5310 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2334 raw5310; decide +kernel
    rw [heq]
    exact (canonical5310 hH).trans (sound522 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2334 (1 : Fin 4)) =
      Sparse.eval value1084 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2334 (1 : Fin 4) = raw5250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2334 raw5250; decide +kernel
    rw [heq]
    exact (canonical5250 hH).trans (sound1084 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2334 (2 : Fin 4)) =
      Sparse.eval value718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2334 (2 : Fin 4) = raw5245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2334 raw5245; decide +kernel
    rw [heq]
    exact (canonical5245 hH).trans (sound718 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2334 (3 : Fin 4)) =
      Sparse.eval value714 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2334 (3 : Fin 4) = raw5244 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2334 raw5244; decide +kernel
    rw [heq]
    exact (canonical5244 hH).trans (sound714 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2334 + (injectiveMoment H (mergeFirst pivotMatrix2334 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2334 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2334 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2334 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2334, value1084, value522, value714, value718, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2335 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2335 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 0, 1, -2]]

theorem sound2335 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2335 = Sparse.eval value2335 (momentVector H) := by
  have heq : pivotMatrix2335 = (fun u v => node2335 (pivotPermutation2335 u) v) := by apply Matrix.ext; unfold pivotMatrix2335 node2335 pivotPermutation2335; decide +kernel
  have hmoment : injectiveMoment H node2335 = injectiveMoment H pivotMatrix2335 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2335 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2335 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2335 (0 : Fin 4)) =
      Sparse.eval value1253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2335 (0 : Fin 4) = raw7811 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2335 raw7811; decide +kernel
    rw [heq]
    exact (canonical7811 hH).trans (sound1253 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2335 (1 : Fin 4)) =
      Sparse.eval value410 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2335 (1 : Fin 4) = raw5302 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2335 raw5302; decide +kernel
    rw [heq]
    exact (canonical5302 hH).trans (sound410 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2335 (2 : Fin 4)) =
      Sparse.eval value718 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2335 (2 : Fin 4) = raw5245 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2335 raw5245; decide +kernel
    rw [heq]
    exact (canonical5245 hH).trans (sound718 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2335 (3 : Fin 4)) =
      Sparse.eval value681 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2335 (3 : Fin 4) = raw5242 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2335 raw5242; decide +kernel
    rw [heq]
    exact (canonical5242 hH).trans (sound681 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2335 + (injectiveMoment H (mergeFirst pivotMatrix2335 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2335 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2335 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2335 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2335, value1253, value410, value681, value718, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2336 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2336 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound2336 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2336 = Sparse.eval value2336 (momentVector H) := by
  have heq : pivotMatrix2336 = (fun u v => node2336 (pivotPermutation2336 u) v) := by apply Matrix.ext; unfold pivotMatrix2336 node2336 pivotPermutation2336; decide +kernel
  have hmoment : injectiveMoment H node2336 = injectiveMoment H pivotMatrix2336 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2336 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2336 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2336 (0 : Fin 4)) =
      Sparse.eval value1206 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2336 (0 : Fin 4) = raw4539 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2336 raw4539; decide +kernel
    rw [heq]
    exact (canonical4539 hH).trans (sound1206 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2336 (1 : Fin 4)) =
      Sparse.eval value1052 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2336 (1 : Fin 4) = raw5249 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2336 raw5249; decide +kernel
    rw [heq]
    exact (canonical5249 hH).trans (sound1052 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2336 (2 : Fin 4)) =
      Sparse.eval value1319 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2336 (2 : Fin 4) = raw5272 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2336 raw5272; decide +kernel
    rw [heq]
    exact (canonical5272 hH).trans (sound1319 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2336 (3 : Fin 4)) =
      Sparse.eval value1205 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2336 (3 : Fin 4) = raw5275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2336 raw5275; decide +kernel
    rw [heq]
    exact (canonical5275 hH).trans (sound1205 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2336 + (injectiveMoment H (mergeFirst pivotMatrix2336 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2336 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2336 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2336 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2336, value1052, value1205, value1206, value1319, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2337 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2337 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound2337 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2337 = Sparse.eval value2337 (momentVector H) := by
  have heq : pivotMatrix2337 = (fun u v => node2337 (pivotPermutation2337 u) v) := by apply Matrix.ext; unfold pivotMatrix2337 node2337 pivotPermutation2337; decide +kernel
  have hmoment : injectiveMoment H node2337 = injectiveMoment H pivotMatrix2337 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2337 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2337 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2337 (0 : Fin 4)) =
      Sparse.eval value1362 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2337 (0 : Fin 4) = raw4540 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2337 raw4540; decide +kernel
    rw [heq]
    exact (canonical4540 hH).trans (sound1362 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2337 (1 : Fin 4)) =
      Sparse.eval value1084 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2337 (1 : Fin 4) = raw5250 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2337 raw5250; decide +kernel
    rw [heq]
    exact (canonical5250 hH).trans (sound1084 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2337 (2 : Fin 4)) =
      Sparse.eval value1370 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2337 (2 : Fin 4) = raw5273 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2337 raw5273; decide +kernel
    rw [heq]
    exact (canonical5273 hH).trans (sound1370 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2337 (3 : Fin 4)) =
      Sparse.eval value1368 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2337 (3 : Fin 4) = raw5276 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2337 raw5276; decide +kernel
    rw [heq]
    exact (canonical5276 hH).trans (sound1368 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2337 + (injectiveMoment H (mergeFirst pivotMatrix2337 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2337 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2337 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2337 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2337, value1084, value1362, value1368, value1370, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2338 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2338 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -2, 2], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound2338 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2338 = Sparse.eval value2338 (momentVector H) := by
  have heq : pivotMatrix2338 = (fun u v => node2338 (pivotPermutation2338 u) v) := by apply Matrix.ext; unfold pivotMatrix2338 node2338 pivotPermutation2338; decide +kernel
  have hmoment : injectiveMoment H node2338 = injectiveMoment H pivotMatrix2338 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2338 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2338 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2338 (0 : Fin 4)) =
      Sparse.eval value1261 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2338 (0 : Fin 4) = raw4541 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2338 raw4541; decide +kernel
    rw [heq]
    exact (canonical4541 hH).trans (sound1261 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2338 (1 : Fin 4)) =
      Sparse.eval value1253 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2338 (1 : Fin 4) = raw5251 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2338 raw5251; decide +kernel
    rw [heq]
    exact (canonical5251 hH).trans (sound1253 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2338 (2 : Fin 4)) =
      Sparse.eval value1219 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2338 (2 : Fin 4) = raw5274 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2338 raw5274; decide +kernel
    rw [heq]
    exact (canonical5274 hH).trans (sound1219 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2338 (3 : Fin 4)) =
      Sparse.eval value1368 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2338 (3 : Fin 4) = raw5277 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2338 raw5277; decide +kernel
    rw [heq]
    exact (canonical5277 hH).trans (sound1368 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2338 + (injectiveMoment H (mergeFirst pivotMatrix2338 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2338 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2338 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2338 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2338, value1219, value1253, value1261, value1368, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2339 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2339 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

theorem sound2339 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2339 = Sparse.eval value2339 (momentVector H) := by
  have heq : pivotMatrix2339 = (fun u v => node2339 (pivotPermutation2339 u) v) := by apply Matrix.ext; unfold pivotMatrix2339 node2339 pivotPermutation2339; decide +kernel
  have hmoment : injectiveMoment H node2339 = injectiveMoment H pivotMatrix2339 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2339 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2339 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2339 (0 : Fin 4)) =
      Sparse.eval value993 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2339 (0 : Fin 4) = raw5219 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2339 raw5219; decide +kernel
    rw [heq]
    exact (canonical5219 hH).trans (sound993 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2339 (1 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2339 (1 : Fin 4) = raw5255 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2339 raw5255; decide +kernel
    rw [heq]
    exact (canonical5255 hH).trans (sound1033 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2339 (2 : Fin 4)) =
      Sparse.eval value500 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2339 (2 : Fin 4) = raw5256 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2339 raw5256; decide +kernel
    rw [heq]
    exact (canonical5256 hH).trans (sound500 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2339 (3 : Fin 4)) =
      Sparse.eval value1033 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2339 (3 : Fin 4) = raw5257 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2339 raw5257; decide +kernel
    rw [heq]
    exact (canonical5257 hH).trans (sound1033 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2339 + (injectiveMoment H (mergeFirst pivotMatrix2339 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2339 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2339 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2339 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2339, value1033, value500, value993, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2340 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2340 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem sound2340 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2340 = Sparse.eval value2340 (momentVector H) := by
  have heq : pivotMatrix2340 = (fun u v => node2340 (pivotPermutation2340 u) v) := by apply Matrix.ext; unfold pivotMatrix2340 node2340 pivotPermutation2340; decide +kernel
  have hmoment : injectiveMoment H node2340 = injectiveMoment H pivotMatrix2340 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2340 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2340 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2340 (0 : Fin 4)) =
      Sparse.eval value955 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2340 (0 : Fin 4) = raw5223 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2340 raw5223; decide +kernel
    rw [heq]
    exact (canonical5223 hH).trans (sound955 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2340 (1 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2340 (1 : Fin 4) = raw5279 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2340 raw5279; decide +kernel
    rw [heq]
    exact (canonical5279 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2340 (2 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2340 (2 : Fin 4) = raw5285 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2340 raw5285; decide +kernel
    rw [heq]
    exact (canonical5285 hH).trans (sound279 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2340 (3 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2340 (3 : Fin 4) = raw5289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2340 raw5289; decide +kernel
    rw [heq]
    exact (canonical5289 hH).trans (sound1027 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2340 + (injectiveMoment H (mergeFirst pivotMatrix2340 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2340 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2340 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2340 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2340, value1027, value279, value955, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2341 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2341 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem sound2341 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2341 = Sparse.eval value2341 (momentVector H) := by
  have heq : pivotMatrix2341 = (fun u v => node2341 (pivotPermutation2341 u) v) := by apply Matrix.ext; unfold pivotMatrix2341 node2341 pivotPermutation2341; decide +kernel
  have hmoment : injectiveMoment H node2341 = injectiveMoment H pivotMatrix2341 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2341 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2341 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2341 (0 : Fin 4)) =
      Sparse.eval value789 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (0 : Fin 4) = raw5225 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5225; decide +kernel
    rw [heq]
    exact (canonical5225 hH).trans (sound789 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2341 (1 : Fin 4)) =
      Sparse.eval value197 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (1 : Fin 4) = raw5281 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5281; decide +kernel
    rw [heq]
    exact (canonical5281 hH).trans (sound197 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2341 (2 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (2 : Fin 4) = raw5289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5289; decide +kernel
    rw [heq]
    exact (canonical5289 hH).trans (sound1027 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2341 (3 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2341 (3 : Fin 4) = raw5292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2341 raw5292; decide +kernel
    rw [heq]
    exact (canonical5292 hH).trans (sound825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2341 + (injectiveMoment H (mergeFirst pivotMatrix2341 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2341 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2341, value1027, value197, value789, value825, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2342 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2342 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound2342 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2342 = Sparse.eval value2342 (momentVector H) := by
  have heq : pivotMatrix2342 = (fun u v => node2342 (pivotPermutation2342 u) v) := by apply Matrix.ext; unfold pivotMatrix2342 node2342 pivotPermutation2342; decide +kernel
  have hmoment : injectiveMoment H node2342 = injectiveMoment H pivotMatrix2342 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2342 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2342 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2342 (0 : Fin 4)) =
      Sparse.eval value1195 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2342 (0 : Fin 4) = raw5226 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2342 raw5226; decide +kernel
    rw [heq]
    exact (canonical5226 hH).trans (sound1195 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2342 (1 : Fin 4)) =
      Sparse.eval value279 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2342 (1 : Fin 4) = raw5282 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2342 raw5282; decide +kernel
    rw [heq]
    exact (canonical5282 hH).trans (sound279 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2342 (2 : Fin 4)) =
      Sparse.eval value1331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2342 (2 : Fin 4) = raw5293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2342 raw5293; decide +kernel
    rw [heq]
    exact (canonical5293 hH).trans (sound1331 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2342 (3 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2342 (3 : Fin 4) = raw5294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2342 raw5294; decide +kernel
    rw [heq]
    exact (canonical5294 hH).trans (sound1237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2342 + (injectiveMoment H (mergeFirst pivotMatrix2342 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2342 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2342 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2342 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2342, value1195, value1237, value1331, value279, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2343 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2343 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound2343 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2343 = Sparse.eval value2343 (momentVector H) := by
  have heq : pivotMatrix2343 = (fun u v => node2343 (pivotPermutation2343 u) v) := by apply Matrix.ext; unfold pivotMatrix2343 node2343 pivotPermutation2343; decide +kernel
  have hmoment : injectiveMoment H node2343 = injectiveMoment H pivotMatrix2343 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2343 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2343 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2343 (0 : Fin 4)) =
      Sparse.eval value930 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2343 (0 : Fin 4) = raw5227 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2343 raw5227; decide +kernel
    rw [heq]
    exact (canonical5227 hH).trans (sound930 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2343 (1 : Fin 4)) =
      Sparse.eval value275 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2343 (1 : Fin 4) = raw5283 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2343 raw5283; decide +kernel
    rw [heq]
    exact (canonical5283 hH).trans (sound275 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2343 (2 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2343 (2 : Fin 4) = raw5294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2343 raw5294; decide +kernel
    rw [heq]
    exact (canonical5294 hH).trans (sound1237 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2343 (3 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2343 (3 : Fin 4) = raw5295 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2343 raw5295; decide +kernel
    rw [heq]
    exact (canonical5295 hH).trans (sound1237 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2343 + (injectiveMoment H (mergeFirst pivotMatrix2343 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2343 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2343 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2343 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2343, value1237, value275, value930, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2344 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2344 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem sound2344 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2344 = Sparse.eval value2344 (momentVector H) := by
  have heq : pivotMatrix2344 = (fun u v => node2344 (pivotPermutation2344 u) v) := by apply Matrix.ext; unfold pivotMatrix2344 node2344 pivotPermutation2344; decide +kernel
  have hmoment : injectiveMoment H node2344 = injectiveMoment H pivotMatrix2344 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2344 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2344 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2344 (0 : Fin 4)) =
      Sparse.eval value991 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2344 (0 : Fin 4) = raw5230 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2344 raw5230; decide +kernel
    rw [heq]
    exact (canonical5230 hH).trans (sound991 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2344 (1 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2344 (1 : Fin 4) = raw5294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2344 raw5294; decide +kernel
    rw [heq]
    exact (canonical5294 hH).trans (sound1237 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2344 (2 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2344 (2 : Fin 4) = raw5298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2344 raw5298; decide +kernel
    rw [heq]
    exact (canonical5298 hH).trans (sound497 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2344 (3 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2344 (3 : Fin 4) = raw5299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2344 raw5299; decide +kernel
    rw [heq]
    exact (canonical5299 hH).trans (sound1027 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2344 + (injectiveMoment H (mergeFirst pivotMatrix2344 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2344 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2344 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2344 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2344, value1027, value1237, value497, value991, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2345 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2345 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

theorem sound2345 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2345 = Sparse.eval value2345 (momentVector H) := by
  have heq : pivotMatrix2345 = (fun u v => node2345 (pivotPermutation2345 u) v) := by apply Matrix.ext; unfold pivotMatrix2345 node2345 pivotPermutation2345; decide +kernel
  have hmoment : injectiveMoment H node2345 = injectiveMoment H pivotMatrix2345 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2345 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2345 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2345 (0 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2345 (0 : Fin 4) = raw5363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2345 raw5363; decide +kernel
    rw [heq]
    exact (canonical5363 hH).trans (sound1107 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2345 (1 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2345 (1 : Fin 4) = raw5296 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2345 raw5296; decide +kernel
    rw [heq]
    exact (canonical5296 hH).trans (sound825 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2345 (2 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2345 (2 : Fin 4) = raw5292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2345 raw5292; decide +kernel
    rw [heq]
    exact (canonical5292 hH).trans (sound825 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2345 (3 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2345 (3 : Fin 4) = raw5289 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2345 raw5289; decide +kernel
    rw [heq]
    exact (canonical5289 hH).trans (sound1027 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2345 + (injectiveMoment H (mergeFirst pivotMatrix2345 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2345 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2345 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2345 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2345, value1027, value1107, value825, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2346 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2346 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem sound2346 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2346 = Sparse.eval value2346 (momentVector H) := by
  have heq : pivotMatrix2346 = (fun u v => node2346 (pivotPermutation2346 u) v) := by apply Matrix.ext; unfold pivotMatrix2346 node2346 pivotPermutation2346; decide +kernel
  have hmoment : injectiveMoment H node2346 = injectiveMoment H pivotMatrix2346 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2346 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2346 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2346 (0 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2346 (0 : Fin 4) = raw5368 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2346 raw5368; decide +kernel
    rw [heq]
    exact (canonical5368 hH).trans (sound1096 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2346 (1 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2346 (1 : Fin 4) = raw5298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2346 raw5298; decide +kernel
    rw [heq]
    exact (canonical5298 hH).trans (sound497 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2346 (2 : Fin 4)) =
      Sparse.eval value1237 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2346 (2 : Fin 4) = raw5294 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2346 raw5294; decide +kernel
    rw [heq]
    exact (canonical5294 hH).trans (sound1237 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2346 (3 : Fin 4)) =
      Sparse.eval value1331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2346 (3 : Fin 4) = raw5293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2346 raw5293; decide +kernel
    rw [heq]
    exact (canonical5293 hH).trans (sound1331 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2346 + (injectiveMoment H (mergeFirst pivotMatrix2346 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2346 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2346 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2346 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2346, value1096, value1237, value1331, value497, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2347 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2347 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -2, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem sound2347 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2347 = Sparse.eval value2347 (momentVector H) := by
  have heq : pivotMatrix2347 = (fun u v => node2347 (pivotPermutation2347 u) v) := by apply Matrix.ext; unfold pivotMatrix2347 node2347 pivotPermutation2347; decide +kernel
  have hmoment : injectiveMoment H node2347 = injectiveMoment H pivotMatrix2347 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2347 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2347 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2347 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2347 (0 : Fin 4) = raw5371 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2347 raw5371; decide +kernel
    rw [heq]
    exact (canonical5371 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2347 (1 : Fin 4)) =
      Sparse.eval value1012 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2347 (1 : Fin 4) = raw5301 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2347 raw5301; decide +kernel
    rw [heq]
    exact (canonical5301 hH).trans (sound1012 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2347 (2 : Fin 4)) =
      Sparse.eval value1027 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2347 (2 : Fin 4) = raw5299 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2347 raw5299; decide +kernel
    rw [heq]
    exact (canonical5299 hH).trans (sound1027 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2347 (3 : Fin 4)) =
      Sparse.eval value497 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2347 (3 : Fin 4) = raw5298 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2347 raw5298; decide +kernel
    rw [heq]
    exact (canonical5298 hH).trans (sound497 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2347 + (injectiveMoment H (mergeFirst pivotMatrix2347 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2347 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2347 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2347 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2347, value1005, value1012, value1027, value497, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2348 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2348 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem sound2348 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2348 = Sparse.eval value2348 (momentVector H) := by
  have heq : pivotMatrix2348 = (fun u v => node2348 (pivotPermutation2348 u) v) := by apply Matrix.ext; unfold pivotMatrix2348 node2348 pivotPermutation2348; decide +kernel
  have hmoment : injectiveMoment H node2348 = injectiveMoment H pivotMatrix2348 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2348 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2348 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2348 (0 : Fin 4)) =
      Sparse.eval value1014 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (0 : Fin 4) = raw5243 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5243; decide +kernel
    rw [heq]
    exact (canonical5243 hH).trans (sound1014 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2348 (1 : Fin 4)) =
      Sparse.eval value1154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (1 : Fin 4) = raw5305 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5305; decide +kernel
    rw [heq]
    exact (canonical5305 hH).trans (sound1154 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2348 (2 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (2 : Fin 4) = raw5308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5308; decide +kernel
    rw [heq]
    exact (canonical5308 hH).trans (sound453 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2348 (3 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2348 (3 : Fin 4) = raw5309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2348 raw5309; decide +kernel
    rw [heq]
    exact (canonical5309 hH).trans (sound1007 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2348 + (injectiveMoment H (mergeFirst pivotMatrix2348 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2348 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2348, value1007, value1014, value1154, value453, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2349 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2349 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

theorem sound2349 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2349 = Sparse.eval value2349 (momentVector H) := by
  have heq : pivotMatrix2349 = (fun u v => node2349 (pivotPermutation2349 u) v) := by apply Matrix.ext; unfold pivotMatrix2349 node2349 pivotPermutation2349; decide +kernel
  have hmoment : injectiveMoment H node2349 = injectiveMoment H pivotMatrix2349 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2349 0 = Pi.single (3 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2349 3 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2349 (0 : Fin 4)) =
      Sparse.eval value893 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2349 (0 : Fin 4) = raw4538 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2349 raw4538; decide +kernel
    rw [heq]
    exact (canonical4538 hH).trans (sound893 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2349 (1 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2349 (1 : Fin 4) = raw5308 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2349 raw5308; decide +kernel
    rw [heq]
    exact (canonical5308 hH).trans (sound453 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2349 (2 : Fin 4)) =
      Sparse.eval value757 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2349 (2 : Fin 4) = raw5348 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2349 raw5348; decide +kernel
    rw [heq]
    exact (canonical5348 hH).trans (sound757 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2349 (3 : Fin 4)) =
      Sparse.eval value941 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2349 (3 : Fin 4) = raw5349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2349 raw5349; decide +kernel
    rw [heq]
    exact (canonical5349 hH).trans (sound941 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2349 + (injectiveMoment H (mergeFirst pivotMatrix2349 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2349 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2349 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2349 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2349, value453, value757, value893, value941, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2350 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2350 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -1, 1, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound2350 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2350 = Sparse.eval value2350 (momentVector H) := by
  have heq : pivotMatrix2350 = (fun u v => node2350 (pivotPermutation2350 u) v) := by apply Matrix.ext; unfold pivotMatrix2350 node2350 pivotPermutation2350; decide +kernel
  have hmoment : injectiveMoment H node2350 = injectiveMoment H pivotMatrix2350 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2350 0 = Pi.single (2 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2350 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2350 (0 : Fin 4)) =
      Sparse.eval value1296 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2350 (0 : Fin 4) = raw4747 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2350 raw4747; decide +kernel
    rw [heq]
    exact (canonical4747 hH).trans (sound1296 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2350 (1 : Fin 4)) =
      Sparse.eval value1007 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2350 (1 : Fin 4) = raw5309 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2350 raw5309; decide +kernel
    rw [heq]
    exact (canonical5309 hH).trans (sound1007 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2350 (2 : Fin 4)) =
      Sparse.eval value588 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2350 (2 : Fin 4) = raw5327 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2350 raw5327; decide +kernel
    rw [heq]
    exact (canonical5327 hH).trans (sound588 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2350 (3 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2350 (3 : Fin 4) = raw5330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2350 raw5330; decide +kernel
    rw [heq]
    exact (canonical5330 hH).trans (sound1303 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2350 + (injectiveMoment H (mergeFirst pivotMatrix2350 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2350 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2350 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2350 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2350, value1007, value1296, value1303, value588, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2351 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2351 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![2, -2, 1, -1]]

theorem sound2351 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2351 = Sparse.eval value2351 (momentVector H) := by
  have heq : pivotMatrix2351 = (fun u v => node2351 (pivotPermutation2351 u) v) := by apply Matrix.ext; unfold pivotMatrix2351 node2351 pivotPermutation2351; decide +kernel
  have hmoment : injectiveMoment H node2351 = injectiveMoment H pivotMatrix2351 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2351 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2351 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2351 (0 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2351 (0 : Fin 4) = raw5421 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2351 raw5421; decide +kernel
    rw [heq]
    exact (canonical5421 hH).trans (sound1304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2351 (1 : Fin 4)) =
      Sparse.eval value1344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2351 (1 : Fin 4) = raw5345 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2351 raw5345; decide +kernel
    rw [heq]
    exact (canonical5345 hH).trans (sound1344 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2351 (2 : Fin 4)) =
      Sparse.eval value719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2351 (2 : Fin 4) = raw5323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2351 raw5323; decide +kernel
    rw [heq]
    exact (canonical5323 hH).trans (sound719 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2351 (3 : Fin 4)) =
      Sparse.eval value1377 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2351 (3 : Fin 4) = raw5320 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2351 raw5320; decide +kernel
    rw [heq]
    exact (canonical5320 hH).trans (sound1377 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2351 + (injectiveMoment H (mergeFirst pivotMatrix2351 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2351 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2351 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2351 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2351, value1304, value1344, value1377, value719, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2352 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2352 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 0, 0]]

theorem sound2352 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2352 = Sparse.eval value2352 (momentVector H) := by
  have heq : pivotMatrix2352 = (fun u v => node2352 (pivotPermutation2352 u) v) := by apply Matrix.ext; unfold pivotMatrix2352 node2352 pivotPermutation2352; decide +kernel
  have hmoment : injectiveMoment H node2352 = injectiveMoment H pivotMatrix2352 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2352 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2352 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2352 (0 : Fin 4)) =
      Sparse.eval value605 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (0 : Fin 4) = raw5423 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5423; decide +kernel
    rw [heq]
    exact (canonical5423 hH).trans (sound605 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2352 (1 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (1 : Fin 4) = raw5347 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5347; decide +kernel
    rw [heq]
    exact (canonical5347 hH).trans (sound1304 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2352 (2 : Fin 4)) =
      Sparse.eval value587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (2 : Fin 4) = raw5325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5325; decide +kernel
    rw [heq]
    exact (canonical5325 hH).trans (sound587 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2352 (3 : Fin 4)) =
      Sparse.eval value719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2352 (3 : Fin 4) = raw5323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2352 raw5323; decide +kernel
    rw [heq]
    exact (canonical5323 hH).trans (sound719 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2352 + (injectiveMoment H (mergeFirst pivotMatrix2352 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2352 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2352, value1304, value587, value605, value719, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2353 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2353 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

theorem sound2353 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2353 = Sparse.eval value2353 (momentVector H) := by
  have heq : pivotMatrix2353 = (fun u v => node2353 (pivotPermutation2353 u) v) := by apply Matrix.ext; unfold pivotMatrix2353 node2353 pivotPermutation2353; decide +kernel
  have hmoment : injectiveMoment H node2353 = injectiveMoment H pivotMatrix2353 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2353 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2353 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2353 (0 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2353 (0 : Fin 4) = raw5425 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2353 raw5425; decide +kernel
    rw [heq]
    exact (canonical5425 hH).trans (sound1304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2353 (1 : Fin 4)) =
      Sparse.eval value1244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2353 (1 : Fin 4) = raw5350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2353 raw5350; decide +kernel
    rw [heq]
    exact (canonical5350 hH).trans (sound1244 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2353 (2 : Fin 4)) =
      Sparse.eval value678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2353 (2 : Fin 4) = raw5331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2353 raw5331; decide +kernel
    rw [heq]
    exact (canonical5331 hH).trans (sound678 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2353 (3 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2353 (3 : Fin 4) = raw5330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2353 raw5330; decide +kernel
    rw [heq]
    exact (canonical5330 hH).trans (sound1303 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2353 + (injectiveMoment H (mergeFirst pivotMatrix2353 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2353 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2353 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2353 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2353, value1244, value1303, value1304, value678, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2354 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2354 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, -1, 1, -1]]

theorem sound2354 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2354 = Sparse.eval value2354 (momentVector H) := by
  have heq : pivotMatrix2354 = (fun u v => node2354 (pivotPermutation2354 u) v) := by apply Matrix.ext; unfold pivotMatrix2354 node2354 pivotPermutation2354; decide +kernel
  have hmoment : injectiveMoment H node2354 = injectiveMoment H pivotMatrix2354 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2354 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2354 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2354 (0 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2354 (0 : Fin 4) = raw5426 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2354 raw5426; decide +kernel
    rw [heq]
    exact (canonical5426 hH).trans (sound608 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2354 (1 : Fin 4)) =
      Sparse.eval value1360 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2354 (1 : Fin 4) = raw5351 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2354 raw5351; decide +kernel
    rw [heq]
    exact (canonical5351 hH).trans (sound1360 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2354 (2 : Fin 4)) =
      Sparse.eval value678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2354 (2 : Fin 4) = raw5332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2354 raw5332; decide +kernel
    rw [heq]
    exact (canonical5332 hH).trans (sound678 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2354 (3 : Fin 4)) =
      Sparse.eval value678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2354 (3 : Fin 4) = raw5331 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2354 raw5331; decide +kernel
    rw [heq]
    exact (canonical5331 hH).trans (sound678 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2354 + (injectiveMoment H (mergeFirst pivotMatrix2354 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2354 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2354 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2354 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2354, value1360, value608, value678, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2355 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2355 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

theorem sound2355 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2355 = Sparse.eval value2355 (momentVector H) := by
  have heq : pivotMatrix2355 = (fun u v => node2355 (pivotPermutation2355 u) v) := by apply Matrix.ext; unfold pivotMatrix2355 node2355 pivotPermutation2355; decide +kernel
  have hmoment : injectiveMoment H node2355 = injectiveMoment H pivotMatrix2355 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2355 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2355 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2355 (0 : Fin 4)) =
      Sparse.eval value1344 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2355 (0 : Fin 4) = raw7842 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2355 raw7842; decide +kernel
    rw [heq]
    exact (canonical7842 hH).trans (sound1344 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2355 (1 : Fin 4)) =
      Sparse.eval value503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2355 (1 : Fin 4) = raw5375 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2355 raw5375; decide +kernel
    rw [heq]
    exact (canonical5375 hH).trans (sound503 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2355 (2 : Fin 4)) =
      Sparse.eval value678 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2355 (2 : Fin 4) = raw5332 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2355 raw5332; decide +kernel
    rw [heq]
    exact (canonical5332 hH).trans (sound678 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2355 (3 : Fin 4)) =
      Sparse.eval value719 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2355 (3 : Fin 4) = raw5323 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2355 raw5323; decide +kernel
    rw [heq]
    exact (canonical5323 hH).trans (sound719 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2355 + (injectiveMoment H (mergeFirst pivotMatrix2355 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2355 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2355 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2355 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2355, value1344, value503, value678, value719, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2356 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2356 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

theorem sound2356 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2356 = Sparse.eval value2356 (momentVector H) := by
  have heq : pivotMatrix2356 = (fun u v => node2356 (pivotPermutation2356 u) v) := by apply Matrix.ext; unfold pivotMatrix2356 node2356 pivotPermutation2356; decide +kernel
  have hmoment : injectiveMoment H node2356 = injectiveMoment H pivotMatrix2356 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2356 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2356 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2356 (0 : Fin 4)) =
      Sparse.eval value1345 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2356 (0 : Fin 4) = raw7843 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2356 raw7843; decide +kernel
    rw [heq]
    exact (canonical7843 hH).trans (sound1345 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2356 (1 : Fin 4)) =
      Sparse.eval value989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2356 (1 : Fin 4) = raw5376 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2356 raw5376; decide +kernel
    rw [heq]
    exact (canonical5376 hH).trans (sound989 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2356 (2 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2356 (2 : Fin 4) = raw5333 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2356 raw5333; decide +kernel
    rw [heq]
    exact (canonical5333 hH).trans (sound1303 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2356 (3 : Fin 4)) =
      Sparse.eval value587 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2356 (3 : Fin 4) = raw5325 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2356 raw5325; decide +kernel
    rw [heq]
    exact (canonical5325 hH).trans (sound587 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2356 + (injectiveMoment H (mergeFirst pivotMatrix2356 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2356 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2356 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2356 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2356, value1303, value1345, value587, value989, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2357 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2357 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem sound2357 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2357 = Sparse.eval value2357 (momentVector H) := by
  have heq : pivotMatrix2357 = (fun u v => node2357 (pivotPermutation2357 u) v) := by apply Matrix.ext; unfold pivotMatrix2357 node2357 pivotPermutation2357; decide +kernel
  have hmoment : injectiveMoment H node2357 = injectiveMoment H pivotMatrix2357 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2357 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2357 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2357 (0 : Fin 4)) =
      Sparse.eval value1205 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2357 (0 : Fin 4) = raw5275 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2357 raw5275; decide +kernel
    rw [heq]
    exact (canonical5275 hH).trans (sound1205 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2357 (1 : Fin 4)) =
      Sparse.eval value1303 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2357 (1 : Fin 4) = raw5330 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2357 raw5330; decide +kernel
    rw [heq]
    exact (canonical5330 hH).trans (sound1303 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2357 (2 : Fin 4)) =
      Sparse.eval value941 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2357 (2 : Fin 4) = raw5349 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2357 raw5349; decide +kernel
    rw [heq]
    exact (canonical5349 hH).trans (sound941 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2357 (3 : Fin 4)) =
      Sparse.eval value1244 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2357 (3 : Fin 4) = raw5350 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2357 raw5350; decide +kernel
    rw [heq]
    exact (canonical5350 hH).trans (sound1244 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2357 + (injectiveMoment H (mergeFirst pivotMatrix2357 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2357 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2357 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2357 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2357, value1205, value1244, value1303, value941, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2358 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2358 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

theorem sound2358 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2358 = Sparse.eval value2358 (momentVector H) := by
  have heq : pivotMatrix2358 = (fun u v => node2358 (pivotPermutation2358 u) v) := by apply Matrix.ext; unfold pivotMatrix2358 node2358 pivotPermutation2358; decide +kernel
  have hmoment : injectiveMoment H node2358 = injectiveMoment H pivotMatrix2358 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2358 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2358 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2358 (0 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (0 : Fin 4) = raw5292 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5292; decide +kernel
    rw [heq]
    exact (canonical5292 hH).trans (sound825 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2358 (1 : Fin 4)) =
      Sparse.eval value224 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (1 : Fin 4) = raw5355 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5355; decide +kernel
    rw [heq]
    exact (canonical5355 hH).trans (sound224 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2358 (2 : Fin 4)) =
      Sparse.eval value1107 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (2 : Fin 4) = raw5363 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5363; decide +kernel
    rw [heq]
    exact (canonical5363 hH).trans (sound1107 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2358 (3 : Fin 4)) =
      Sparse.eval value825 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2358 (3 : Fin 4) = raw5366 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2358 raw5366; decide +kernel
    rw [heq]
    exact (canonical5366 hH).trans (sound825 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2358 + (injectiveMoment H (mergeFirst pivotMatrix2358 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2358 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2358, value1107, value224, value825, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2359 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2359 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

theorem sound2359 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2359 = Sparse.eval value2359 (momentVector H) := by
  have heq : pivotMatrix2359 = (fun u v => node2359 (pivotPermutation2359 u) v) := by apply Matrix.ext; unfold pivotMatrix2359 node2359 pivotPermutation2359; decide +kernel
  have hmoment : injectiveMoment H node2359 = injectiveMoment H pivotMatrix2359 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2359 0 = Pi.single (3 : Fin 4) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2359 3 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2359 (0 : Fin 4)) =
      Sparse.eval value1331 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2359 (0 : Fin 4) = raw5293 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2359 raw5293; decide +kernel
    rw [heq]
    exact (canonical5293 hH).trans (sound1331 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2359 (1 : Fin 4)) =
      Sparse.eval value276 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2359 (1 : Fin 4) = raw5356 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2359 raw5356; decide +kernel
    rw [heq]
    exact (canonical5356 hH).trans (sound276 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2359 (2 : Fin 4)) =
      Sparse.eval value822 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2359 (2 : Fin 4) = raw5367 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2359 raw5367; decide +kernel
    rw [heq]
    exact (canonical5367 hH).trans (sound822 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2359 (3 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2359 (3 : Fin 4) = raw5368 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2359 raw5368; decide +kernel
    rw [heq]
    exact (canonical5368 hH).trans (sound1096 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2359 + (injectiveMoment H (mergeFirst pivotMatrix2359 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2359 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2359 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2359 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2359, value1096, value1331, value276, value822, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2360 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2360 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

theorem sound2360 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2360 = Sparse.eval value2360 (momentVector H) := by
  have heq : pivotMatrix2360 = (fun u v => node2360 (pivotPermutation2360 u) v) := by apply Matrix.ext; unfold pivotMatrix2360 node2360 pivotPermutation2360; decide +kernel
  have hmoment : injectiveMoment H node2360 = injectiveMoment H pivotMatrix2360 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2360 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2360 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2360 (0 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2360 (0 : Fin 4) = raw5440 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2360 raw5440; decide +kernel
    rw [heq]
    exact (canonical5440 hH).trans (sound1005 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2360 (1 : Fin 4)) =
      Sparse.eval value503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2360 (1 : Fin 4) = raw5370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2360 raw5370; decide +kernel
    rw [heq]
    exact (canonical5370 hH).trans (sound503 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2360 (2 : Fin 4)) =
      Sparse.eval value1096 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2360 (2 : Fin 4) = raw5368 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2360 raw5368; decide +kernel
    rw [heq]
    exact (canonical5368 hH).trans (sound1096 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2360 (3 : Fin 4)) =
      Sparse.eval value822 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2360 (3 : Fin 4) = raw5367 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2360 raw5367; decide +kernel
    rw [heq]
    exact (canonical5367 hH).trans (sound822 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2360 + (injectiveMoment H (mergeFirst pivotMatrix2360 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2360 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2360 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2360 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2360, value1005, value1096, value503, value822, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2361 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2361 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

theorem sound2361 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2361 = Sparse.eval value2361 (momentVector H) := by
  have heq : pivotMatrix2361 = (fun u v => node2361 (pivotPermutation2361 u) v) := by apply Matrix.ext; unfold pivotMatrix2361 node2361 pivotPermutation2361; decide +kernel
  have hmoment : injectiveMoment H node2361 = injectiveMoment H pivotMatrix2361 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2361 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2361 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2361 (0 : Fin 4)) =
      Sparse.eval value1304 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2361 (0 : Fin 4) = raw5441 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2361 raw5441; decide +kernel
    rw [heq]
    exact (canonical5441 hH).trans (sound1304 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2361 (1 : Fin 4)) =
      Sparse.eval value989 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2361 (1 : Fin 4) = raw5373 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2361 raw5373; decide +kernel
    rw [heq]
    exact (canonical5373 hH).trans (sound989 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2361 (2 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2361 (2 : Fin 4) = raw5371 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2361 raw5371; decide +kernel
    rw [heq]
    exact (canonical5371 hH).trans (sound1005 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2361 (3 : Fin 4)) =
      Sparse.eval value503 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2361 (3 : Fin 4) = raw5370 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2361 raw5370; decide +kernel
    rw [heq]
    exact (canonical5370 hH).trans (sound503 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2361 + (injectiveMoment H (mergeFirst pivotMatrix2361 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2361 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2361 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2361 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2361, value1005, value1304, value503, value989, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2362 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2362 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

theorem sound2362 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2362 = Sparse.eval value2362 (momentVector H) := by
  have heq : pivotMatrix2362 = (fun u v => node2362 (pivotPermutation2362 u) v) := by apply Matrix.ext; unfold pivotMatrix2362 node2362 pivotPermutation2362; decide +kernel
  have hmoment : injectiveMoment H node2362 = injectiveMoment H pivotMatrix2362 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2362 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2362 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2362 (0 : Fin 4)) =
      Sparse.eval value608 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2362 (0 : Fin 4) = raw5442 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2362 raw5442; decide +kernel
    rw [heq]
    exact (canonical5442 hH).trans (sound608 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2362 (1 : Fin 4)) =
      Sparse.eval value720 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2362 (1 : Fin 4) = raw5374 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2362 raw5374; decide +kernel
    rw [heq]
    exact (canonical5374 hH).trans (sound720 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2362 (2 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2362 (2 : Fin 4) = raw5372 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2362 raw5372; decide +kernel
    rw [heq]
    exact (canonical5372 hH).trans (sound1005 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2362 (3 : Fin 4)) =
      Sparse.eval value1005 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2362 (3 : Fin 4) = raw5371 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2362 raw5371; decide +kernel
    rw [heq]
    exact (canonical5371 hH).trans (sound1005 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2362 + (injectiveMoment H (mergeFirst pivotMatrix2362 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2362 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2362 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2362 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2362, value1005, value608, value720, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2363 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2363 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 0, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 1, -2]]

theorem sound2363 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2363 = Sparse.eval value2363 (momentVector H) := by
  have heq : pivotMatrix2363 = (fun u v => node2363 (pivotPermutation2363 u) v) := by apply Matrix.ext; unfold pivotMatrix2363 node2363 pivotPermutation2363; decide +kernel
  have hmoment : injectiveMoment H node2363 = injectiveMoment H pivotMatrix2363 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2363 0 = Pi.single (0 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2363 0 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2363 (0 : Fin 4)) =
      Sparse.eval value1278 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2363 (0 : Fin 4) = raw7968 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2363 raw7968; decide +kernel
    rw [heq]
    exact (canonical7968 hH).trans (sound1278 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2363 (1 : Fin 4)) =
      Sparse.eval value475 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2363 (1 : Fin 4) = raw5444 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2363 raw5444; decide +kernel
    rw [heq]
    exact (canonical5444 hH).trans (sound475 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2363 (2 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2363 (2 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2363 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2363 (3 : Fin 4)) =
      Sparse.eval value595 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2363 (3 : Fin 4) = raw5388 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2363 raw5388; decide +kernel
    rw [heq]
    exact (canonical5388 hH).trans (sound595 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2363 + (injectiveMoment H (mergeFirst pivotMatrix2363 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2363 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2363 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2363 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2363, value1278, value475, value584, value595, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2364 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2364 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 0, 0], ![1, 0, 2, -3]]

theorem sound2364 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2364 = Sparse.eval value2364 (momentVector H) := by
  have heq : pivotMatrix2364 = (fun u v => node2364 (pivotPermutation2364 u) v) := by apply Matrix.ext; unfold pivotMatrix2364 node2364 pivotPermutation2364; decide +kernel
  have hmoment : injectiveMoment H node2364 = injectiveMoment H pivotMatrix2364 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2364 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2364 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2364 (0 : Fin 4)) =
      Sparse.eval value1154 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (0 : Fin 4) = raw5448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5448; decide +kernel
    rw [heq]
    exact (canonical5448 hH).trans (sound1154 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2364 (1 : Fin 4)) =
      Sparse.eval value1374 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (1 : Fin 4) = raw5403 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5403; decide +kernel
    rw [heq]
    exact (canonical5403 hH).trans (sound1374 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2364 (2 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (2 : Fin 4) = raw5397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5397; decide +kernel
    rw [heq]
    exact (canonical5397 hH).trans (sound688 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2364 (3 : Fin 4)) =
      Sparse.eval value1373 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2364 (3 : Fin 4) = raw5396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2364 raw5396; decide +kernel
    rw [heq]
    exact (canonical5396 hH).trans (sound1373 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2364 + (injectiveMoment H (mergeFirst pivotMatrix2364 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2364 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2364, value1154, value1373, value1374, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2365 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2365 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem sound2365 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2365 = Sparse.eval value2365 (momentVector H) := by
  have heq : pivotMatrix2365 = (fun u v => node2365 (pivotPermutation2365 u) v) := by apply Matrix.ext; unfold pivotMatrix2365 node2365 pivotPermutation2365; decide +kernel
  have hmoment : injectiveMoment H node2365 = injectiveMoment H pivotMatrix2365 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2365 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2365 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2365 (0 : Fin 4)) =
      Sparse.eval value453 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (0 : Fin 4) = raw5449 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5449; decide +kernel
    rw [heq]
    exact (canonical5449 hH).trans (sound453 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2365 (1 : Fin 4)) =
      Sparse.eval value476 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (1 : Fin 4) = raw5404 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5404; decide +kernel
    rw [heq]
    exact (canonical5404 hH).trans (sound476 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2365 (2 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (2 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2365 (3 : Fin 4)) =
      Sparse.eval value688 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2365 (3 : Fin 4) = raw5397 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2365 raw5397; decide +kernel
    rw [heq]
    exact (canonical5397 hH).trans (sound688 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2365 + (injectiveMoment H (mergeFirst pivotMatrix2365 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2365 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2365, value453, value476, value584, value688, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2366 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2366 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 0, 1, -1], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem sound2366 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2366 = Sparse.eval value2366 (momentVector H) := by
  have heq : pivotMatrix2366 = (fun u v => node2366 (pivotPermutation2366 u) v) := by apply Matrix.ext; unfold pivotMatrix2366 node2366 pivotPermutation2366; decide +kernel
  have hmoment : injectiveMoment H node2366 = injectiveMoment H pivotMatrix2366 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2366 0 = Pi.single (2 : Fin 4) 1 - Pi.single 3 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2366 2 3 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2366 (0 : Fin 4)) =
      Sparse.eval value758 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2366 (0 : Fin 4) = raw5450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2366 raw5450; decide +kernel
    rw [heq]
    exact (canonical5450 hH).trans (sound758 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2366 (1 : Fin 4)) =
      Sparse.eval value1223 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2366 (1 : Fin 4) = raw5405 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2366 raw5405; decide +kernel
    rw [heq]
    exact (canonical5405 hH).trans (sound1223 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2366 (2 : Fin 4)) =
      Sparse.eval value1183 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2366 (2 : Fin 4) = raw5399 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2366 raw5399; decide +kernel
    rw [heq]
    exact (canonical5399 hH).trans (sound1183 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2366 (3 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2366 (3 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2366 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2366 + (injectiveMoment H (mergeFirst pivotMatrix2366 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2366 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2366 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2366 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2366, value1183, value1223, value584, value758, Sparse.eval] at hc ⊢
  linarith

def pivotPermutation2367 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pivotMatrix2367 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, -1, 0, 0], ![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, 0, 1, -2]]

theorem sound2367 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2367 = Sparse.eval value2367 (momentVector H) := by
  have heq : pivotMatrix2367 = (fun u v => node2367 (pivotPermutation2367 u) v) := by apply Matrix.ext; unfold pivotMatrix2367 node2367 pivotPermutation2367; decide +kernel
  have hmoment : injectiveMoment H node2367 = injectiveMoment H pivotMatrix2367 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2367 0 = Pi.single (0 : Fin 4) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix2367 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2367 (0 : Fin 4)) =
      Sparse.eval value1178 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (0 : Fin 4) = raw7896 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw7896; decide +kernel
    rw [heq]
    exact (canonical7896 hH).trans (sound1178 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2367 (1 : Fin 4)) =
      Sparse.eval value394 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (1 : Fin 4) = raw5443 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5443; decide +kernel
    rw [heq]
    exact (canonical5443 hH).trans (sound394 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2367 (2 : Fin 4)) =
      Sparse.eval value584 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (2 : Fin 4) = raw5398 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5398; decide +kernel
    rw [heq]
    exact (canonical5398 hH).trans (sound584 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2367 (3 : Fin 4)) =
      Sparse.eval value576 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2367 (3 : Fin 4) = raw5395 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2367 raw5395; decide +kernel
    rw [heq]
    exact (canonical5395 hH).trans (sound576 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node2367 + (injectiveMoment H (mergeFirst pivotMatrix2367 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix2367 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value2367, value1178, value394, value576, value584, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
