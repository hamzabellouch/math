import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons77

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4928 node4928Labels = Sparse.eval nodeValue4928 (mixedVector B) := by
  have h := singleton4928 B _hB
  rw [sound2318 B _hB _hF, sound3400 B _hB _hF] at h
  norm_num [nodeValue4928, nodeValue2318, nodeValue3400, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = Sparse.eval nodeValue4929 (mixedVector B) := by
  simpa only [nodeValue4929, Sparse.eval_nil] using zero4929 B _hB _hF

theorem sound4930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4930 node4930Labels = Sparse.eval nodeValue4930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4930) = mixedMoment B node4930 node4930Labels := rfl
  simpa [nodeValue4930, Sparse.eval] using hc.symm

theorem sound4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4931 node4931Labels = Sparse.eval nodeValue4931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4931) = mixedMoment B node4931 node4931Labels := rfl
  simpa [nodeValue4931, Sparse.eval] using hc.symm

theorem sound4932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4932 node4932Labels = Sparse.eval nodeValue4932 (mixedVector B) := by
  simpa only [nodeValue4932, Sparse.eval_nil] using zero4932 B _hB _hF

theorem sound4933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4933 node4933Labels = Sparse.eval nodeValue4933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4933) = mixedMoment B node4933 node4933Labels := rfl
  simpa [nodeValue4933, Sparse.eval] using hc.symm

theorem sound4934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4934 node4934Labels = Sparse.eval nodeValue4934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4934) = mixedMoment B node4934 node4934Labels := rfl
  simpa [nodeValue4934, Sparse.eval] using hc.symm

theorem sound4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4935 node4935Labels = Sparse.eval nodeValue4935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4935) = mixedMoment B node4935 node4935Labels := rfl
  simpa [nodeValue4935, Sparse.eval] using hc.symm

theorem sound4936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4936 node4936Labels = Sparse.eval nodeValue4936 (mixedVector B) := by
  have h := singleton4936 B _hB
  rw [sound2328 B _hB _hF, sound3401 B _hB _hF] at h
  norm_num [nodeValue4936, nodeValue2328, nodeValue3401, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4937 node4937Labels = Sparse.eval nodeValue4937 (mixedVector B) := by
  have h := singleton4937 B _hB
  rw [sound2329 B _hB _hF, sound3402 B _hB _hF] at h
  norm_num [nodeValue4937, nodeValue2329, nodeValue3402, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4938 node4938Labels = Sparse.eval nodeValue4938 (mixedVector B) := by
  simpa only [nodeValue4938, Sparse.eval_nil] using zero4938 B _hB _hF

theorem sound4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4939 node4939Labels = Sparse.eval nodeValue4939 (mixedVector B) := by
  have h := singleton4939 B _hB
  rw [sound2330 B _hB _hF, sound3404 B _hB _hF] at h
  norm_num [nodeValue4939, nodeValue2330, nodeValue3404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4940 node4940Labels = Sparse.eval nodeValue4940 (mixedVector B) := by
  simpa only [nodeValue4940, Sparse.eval_nil] using zero4940 B _hB _hF

theorem sound4941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4941 node4941Labels = Sparse.eval nodeValue4941 (mixedVector B) := by
  have h := singleton4941 B _hB
  rw [sound2332 B _hB _hF, sound3410 B _hB _hF] at h
  norm_num [nodeValue4941, nodeValue2332, nodeValue3410, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4942 node4942Labels = Sparse.eval nodeValue4942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4942) = mixedMoment B node4942 node4942Labels := rfl
  simpa [nodeValue4942, Sparse.eval] using hc.symm

theorem sound4943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4943 node4943Labels = Sparse.eval nodeValue4943 (mixedVector B) := by
  have h := singleton4943 B _hB
  rw [sound2334 B _hB _hF, sound3411 B _hB _hF] at h
  norm_num [nodeValue4943, nodeValue2334, nodeValue3411, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4944 node4944Labels = Sparse.eval nodeValue4944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4944) = mixedMoment B node4944 node4944Labels := rfl
  simpa [nodeValue4944, Sparse.eval] using hc.symm

theorem sound4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4945 node4945Labels = Sparse.eval nodeValue4945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4945) = mixedMoment B node4945 node4945Labels := rfl
  simpa [nodeValue4945, Sparse.eval] using hc.symm

theorem sound4946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4946 node4946Labels = Sparse.eval nodeValue4946 (mixedVector B) := by
  have h := singleton4946 B _hB
  rw [sound2337 B _hB _hF, sound3412 B _hB _hF] at h
  norm_num [nodeValue4946, nodeValue2337, nodeValue3412, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4947 node4947Labels = Sparse.eval nodeValue4947 (mixedVector B) := by
  have h := singleton4947 B _hB
  rw [sound2338 B _hB _hF, sound3416 B _hB _hF] at h
  norm_num [nodeValue4947, nodeValue2338, nodeValue3416, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4948 node4948Labels = Sparse.eval nodeValue4948 (mixedVector B) := by
  have h := singleton4948 B _hB
  rw [sound2339 B _hB _hF, sound3420 B _hB _hF] at h
  norm_num [nodeValue4948, nodeValue2339, nodeValue3420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4949 node4949Labels = Sparse.eval nodeValue4949 (mixedVector B) := by
  have h := singleton4949 B _hB
  rw [sound2341 B _hB _hF, sound3417 B _hB _hF] at h
  norm_num [nodeValue4949, nodeValue2341, nodeValue3417, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4950 node4950Labels = Sparse.eval nodeValue4950 (mixedVector B) := by
  have h := singleton4950 B _hB
  rw [sound2342 B _hB _hF, sound3421 B _hB _hF] at h
  norm_num [nodeValue4950, nodeValue2342, nodeValue3421, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4951 node4951Labels = Sparse.eval nodeValue4951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4951) = mixedMoment B node4951 node4951Labels := rfl
  simpa [nodeValue4951, Sparse.eval] using hc.symm

theorem sound4952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4952 node4952Labels = Sparse.eval nodeValue4952 (mixedVector B) := by
  have h := singleton4952 B _hB
  rw [sound2344 B _hB _hF, sound3422 B _hB _hF] at h
  norm_num [nodeValue4952, nodeValue2344, nodeValue3422, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4953 node4953Labels = Sparse.eval nodeValue4953 (mixedVector B) := by
  have h := singleton4953 B _hB
  rw [sound2345 B _hB _hF, sound3423 B _hB _hF] at h
  norm_num [nodeValue4953, nodeValue2345, nodeValue3423, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4954 node4954Labels = Sparse.eval nodeValue4954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4954) = mixedMoment B node4954 node4954Labels := rfl
  simpa [nodeValue4954, Sparse.eval] using hc.symm

theorem sound4955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4955 node4955Labels = Sparse.eval nodeValue4955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4955) = mixedMoment B node4955 node4955Labels := rfl
  simpa [nodeValue4955, Sparse.eval] using hc.symm

theorem sound4956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4956 node4956Labels = Sparse.eval nodeValue4956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4956) = mixedMoment B node4956 node4956Labels := rfl
  simpa [nodeValue4956, Sparse.eval] using hc.symm

theorem sound4957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4957 node4957Labels = Sparse.eval nodeValue4957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4957) = mixedMoment B node4957 node4957Labels := rfl
  simpa [nodeValue4957, Sparse.eval] using hc.symm

theorem sound4958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4958 node4958Labels = Sparse.eval nodeValue4958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4958) = mixedMoment B node4958 node4958Labels := rfl
  simpa [nodeValue4958, Sparse.eval] using hc.symm

theorem sound4959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4959 node4959Labels = Sparse.eval nodeValue4959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4959) = mixedMoment B node4959 node4959Labels := rfl
  simpa [nodeValue4959, Sparse.eval] using hc.symm

theorem sound4960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4960 node4960Labels = Sparse.eval nodeValue4960 (mixedVector B) := by
  have h := singleton4960 B _hB
  rw [sound2412 B _hB _hF, sound3426 B _hB _hF] at h
  norm_num [nodeValue4960, nodeValue2412, nodeValue3426, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4961 node4961Labels = Sparse.eval nodeValue4961 (mixedVector B) := by
  have h := singleton4961 B _hB
  rw [sound2796 B _hB _hF, sound3589 B _hB _hF] at h
  norm_num [nodeValue4961, nodeValue2796, nodeValue3589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4962 node4962Labels = Sparse.eval nodeValue4962 (mixedVector B) := by
  have h := singleton4962 B _hB
  rw [sound2795 B _hB _hF, sound3593 B _hB _hF] at h
  norm_num [nodeValue4962, nodeValue2795, nodeValue3593, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4963 node4963Labels = Sparse.eval nodeValue4963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4963) = mixedMoment B node4963 node4963Labels := rfl
  simpa [nodeValue4963, Sparse.eval] using hc.symm

theorem sound4964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4964 node4964Labels = Sparse.eval nodeValue4964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4964) = mixedMoment B node4964 node4964Labels := rfl
  simpa [nodeValue4964, Sparse.eval] using hc.symm

theorem sound4965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4965 node4965Labels = Sparse.eval nodeValue4965 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4965) = mixedMoment B node4965 node4965Labels := rfl
  simpa [nodeValue4965, Sparse.eval] using hc.symm

theorem sound4966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4966 node4966Labels = Sparse.eval nodeValue4966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4966) = mixedMoment B node4966 node4966Labels := rfl
  simpa [nodeValue4966, Sparse.eval] using hc.symm

theorem sound4967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4967 node4967Labels = Sparse.eval nodeValue4967 (mixedVector B) := by
  have h := singleton4967 B _hB
  rw [sound2814 B _hB _hF, sound3585 B _hB _hF] at h
  norm_num [nodeValue4967, nodeValue2814, nodeValue3585, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4968 node4968Labels = Sparse.eval nodeValue4968 (mixedVector B) := by
  have h := singleton4968 B _hB
  rw [sound2809 B _hB _hF, sound3587 B _hB _hF] at h
  norm_num [nodeValue4968, nodeValue2809, nodeValue3587, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4969 node4969Labels = Sparse.eval nodeValue4969 (mixedVector B) := by
  have h := singleton4969 B _hB
  rw [sound2804 B _hB _hF, sound3586 B _hB _hF] at h
  norm_num [nodeValue4969, nodeValue2804, nodeValue3586, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4970 node4970Labels = Sparse.eval nodeValue4970 (mixedVector B) := by
  have h := singleton4970 B _hB
  rw [sound2815 B _hB _hF, sound3588 B _hB _hF] at h
  norm_num [nodeValue4970, nodeValue2815, nodeValue3588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4971 node4971Labels = Sparse.eval nodeValue4971 (mixedVector B) := by
  have h := singleton4971 B _hB
  rw [sound2807 B _hB _hF, sound3590 B _hB _hF] at h
  norm_num [nodeValue4971, nodeValue2807, nodeValue3590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4972 node4972Labels = Sparse.eval nodeValue4972 (mixedVector B) := by
  have h := singleton4972 B _hB
  rw [sound2434 B _hB _hF, sound3457 B _hB _hF] at h
  norm_num [nodeValue4972, nodeValue2434, nodeValue3457, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4973 node4973Labels = Sparse.eval nodeValue4973 (mixedVector B) := by
  have h := singleton4973 B _hB
  rw [sound2817 B _hB _hF, sound3591 B _hB _hF] at h
  norm_num [nodeValue4973, nodeValue2817, nodeValue3591, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4974 node4974Labels = Sparse.eval nodeValue4974 (mixedVector B) := by
  have h := singleton4974 B _hB
  rw [sound2818 B _hB _hF, sound3592 B _hB _hF] at h
  norm_num [nodeValue4974, nodeValue2818, nodeValue3592, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4975 node4975Labels = Sparse.eval nodeValue4975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4975) = mixedMoment B node4975 node4975Labels := rfl
  simpa [nodeValue4975, Sparse.eval] using hc.symm

theorem sound4976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4976 node4976Labels = Sparse.eval nodeValue4976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4976) = mixedMoment B node4976 node4976Labels := rfl
  simpa [nodeValue4976, Sparse.eval] using hc.symm

theorem sound4977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4977 node4977Labels = Sparse.eval nodeValue4977 (mixedVector B) := by
  have h := singleton4977 B _hB
  rw [sound2813 B _hB _hF, sound3595 B _hB _hF] at h
  norm_num [nodeValue4977, nodeValue2813, nodeValue3595, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4978 node4978Labels = Sparse.eval nodeValue4978 (mixedVector B) := by
  have h := singleton4978 B _hB
  rw [sound2805 B _hB _hF, sound3594 B _hB _hF] at h
  norm_num [nodeValue4978, nodeValue2805, nodeValue3594, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4979 node4979Labels = Sparse.eval nodeValue4979 (mixedVector B) := by
  have h := singleton4979 B _hB
  rw [sound2820 B _hB _hF, sound3596 B _hB _hF] at h
  norm_num [nodeValue4979, nodeValue2820, nodeValue3596, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4980 node4980Labels = Sparse.eval nodeValue4980 (mixedVector B) := by
  have h := singleton4980 B _hB
  rw [sound2366 B _hB _hF, sound2793 B _hB _hF] at h
  norm_num [nodeValue4980, nodeValue2366, nodeValue2793, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4981 node4981Labels = Sparse.eval nodeValue4981 (mixedVector B) := by
  have h := singleton4981 B _hB
  rw [sound2364 B _hB _hF, sound2791 B _hB _hF] at h
  norm_num [nodeValue4981, nodeValue2364, nodeValue2791, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4982 node4982Labels = Sparse.eval nodeValue4982 (mixedVector B) := by
  have h := singleton4982 B _hB
  rw [sound2367 B _hB _hF, sound2421 B _hB _hF] at h
  norm_num [nodeValue4982, nodeValue2367, nodeValue2421, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4983 node4983Labels = Sparse.eval nodeValue4983 (mixedVector B) := by
  have h := singleton4983 B _hB
  rw [sound2368 B _hB _hF, sound2794 B _hB _hF] at h
  norm_num [nodeValue4983, nodeValue2368, nodeValue2794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4984 node4984Labels = Sparse.eval nodeValue4984 (mixedVector B) := by
  have h := singleton4984 B _hB
  rw [sound2365 B _hB _hF, sound2792 B _hB _hF] at h
  norm_num [nodeValue4984, nodeValue2365, nodeValue2792, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4985 node4985Labels = Sparse.eval nodeValue4985 (mixedVector B) := by
  have h := singleton4985 B _hB
  rw [sound2370 B _hB _hF, sound3334 B _hB _hF] at h
  norm_num [nodeValue4985, nodeValue2370, nodeValue3334, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4986 node4986Labels = Sparse.eval nodeValue4986 (mixedVector B) := by
  have h := singleton4986 B _hB
  rw [sound2371 B _hB _hF, sound3335 B _hB _hF] at h
  norm_num [nodeValue4986, nodeValue2371, nodeValue3335, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4987 node4987Labels = Sparse.eval nodeValue4987 (mixedVector B) := by
  have h := singleton4987 B _hB
  rw [sound2372 B _hB _hF, sound3336 B _hB _hF] at h
  norm_num [nodeValue4987, nodeValue2372, nodeValue3336, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4988 node4988Labels = Sparse.eval nodeValue4988 (mixedVector B) := by
  have h := singleton4988 B _hB
  rw [sound2373 B _hB _hF, sound3332 B _hB _hF] at h
  norm_num [nodeValue4988, nodeValue2373, nodeValue3332, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4989 node4989Labels = Sparse.eval nodeValue4989 (mixedVector B) := by
  have h := singleton4989 B _hB
  rw [sound2374 B _hB _hF, sound2413 B _hB _hF] at h
  norm_num [nodeValue4989, nodeValue2374, nodeValue2413, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4990 node4990Labels = Sparse.eval nodeValue4990 (mixedVector B) := by
  have h := singleton4990 B _hB
  rw [sound2375 B _hB _hF, sound3333 B _hB _hF] at h
  norm_num [nodeValue4990, nodeValue2375, nodeValue3333, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4991 node4991Labels = Sparse.eval nodeValue4991 (mixedVector B) := by
  simpa only [nodeValue4991, Sparse.eval_nil] using zero4991 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
