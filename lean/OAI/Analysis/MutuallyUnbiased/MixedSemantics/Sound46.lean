import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons46

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2944 node2944Labels = Sparse.eval nodeValue2944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2944) = mixedMoment B node2944 node2944Labels := rfl
  simpa [nodeValue2944, Sparse.eval] using hc.symm

theorem sound2945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2945 node2945Labels = Sparse.eval nodeValue2945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2945) = mixedMoment B node2945 node2945Labels := rfl
  simpa [nodeValue2945, Sparse.eval] using hc.symm

theorem sound2946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2946 node2946Labels = Sparse.eval nodeValue2946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2946) = mixedMoment B node2946 node2946Labels := rfl
  simpa [nodeValue2946, Sparse.eval] using hc.symm

theorem sound2947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2947 node2947Labels = Sparse.eval nodeValue2947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2947) = mixedMoment B node2947 node2947Labels := rfl
  simpa [nodeValue2947, Sparse.eval] using hc.symm

theorem sound2948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2948 node2948Labels = Sparse.eval nodeValue2948 (mixedVector B) := by
  have h := singleton2948 B _hB
  rw [sound202 B _hB _hF] at h
  norm_num [nodeValue2948, nodeValue202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2949 node2949Labels = Sparse.eval nodeValue2949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2949) = mixedMoment B node2949 node2949Labels := rfl
  simpa [nodeValue2949, Sparse.eval] using hc.symm

theorem sound2950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2950 node2950Labels = Sparse.eval nodeValue2950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2950) = mixedMoment B node2950 node2950Labels := rfl
  simpa [nodeValue2950, Sparse.eval] using hc.symm

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2953 node2953Labels = Sparse.eval nodeValue2953 (mixedVector B) := by
  simpa only [nodeValue2953, Sparse.eval_nil] using zero2953 B _hB _hF

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

theorem sound2956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2956 node2956Labels = Sparse.eval nodeValue2956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2956) = mixedMoment B node2956 node2956Labels := rfl
  simpa [nodeValue2956, Sparse.eval] using hc.symm

theorem sound2957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2957 node2957Labels = Sparse.eval nodeValue2957 (mixedVector B) := by
  have h := singleton2957 B _hB
  rw [sound331 B _hB _hF] at h
  norm_num [nodeValue2957, nodeValue331, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2958 node2958Labels = Sparse.eval nodeValue2958 (mixedVector B) := by
  have h := singleton2958 B _hB
  rw [sound334 B _hB _hF] at h
  norm_num [nodeValue2958, nodeValue334, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2959 node2959Labels = Sparse.eval nodeValue2959 (mixedVector B) := by
  have h := singleton2959 B _hB
  rw [sound339 B _hB _hF] at h
  norm_num [nodeValue2959, nodeValue339, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2960 node2960Labels = Sparse.eval nodeValue2960 (mixedVector B) := by
  have h := singleton2960 B _hB
  rw [sound336 B _hB _hF] at h
  norm_num [nodeValue2960, nodeValue336, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2961 node2961Labels = Sparse.eval nodeValue2961 (mixedVector B) := by
  have h := singleton2961 B _hB
  rw [sound332 B _hB _hF] at h
  norm_num [nodeValue2961, nodeValue332, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2962 node2962Labels = Sparse.eval nodeValue2962 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2962) = mixedMoment B node2962 node2962Labels := rfl
  simpa [nodeValue2962, Sparse.eval] using hc.symm

theorem sound2963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2963 node2963Labels = Sparse.eval nodeValue2963 (mixedVector B) := by
  have h := singleton2963 B _hB
  rw [sound335 B _hB _hF] at h
  norm_num [nodeValue2963, nodeValue335, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2964 node2964Labels = Sparse.eval nodeValue2964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2964) = mixedMoment B node2964 node2964Labels := rfl
  simpa [nodeValue2964, Sparse.eval] using hc.symm

theorem sound2965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2965 node2965Labels = Sparse.eval nodeValue2965 (mixedVector B) := by
  have h := singleton2965 B _hB
  rw [sound338 B _hB _hF] at h
  norm_num [nodeValue2965, nodeValue338, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2966 node2966Labels = Sparse.eval nodeValue2966 (mixedVector B) := by
  have h := singleton2966 B _hB
  rw [sound247 B _hB _hF] at h
  norm_num [nodeValue2966, nodeValue247, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2967 node2967Labels = Sparse.eval nodeValue2967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2967) = mixedMoment B node2967 node2967Labels := rfl
  simpa [nodeValue2967, Sparse.eval] using hc.symm

theorem sound2968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2968 node2968Labels = Sparse.eval nodeValue2968 (mixedVector B) := by
  have h := singleton2968 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2968, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2969 node2969Labels = Sparse.eval nodeValue2969 (mixedVector B) := by
  have h := singleton2969 B _hB
  rw [sound344 B _hB _hF] at h
  norm_num [nodeValue2969, nodeValue344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2970 node2970Labels = Sparse.eval nodeValue2970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2970) = mixedMoment B node2970 node2970Labels := rfl
  simpa [nodeValue2970, Sparse.eval] using hc.symm

theorem sound2971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2971 node2971Labels = Sparse.eval nodeValue2971 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2971) = mixedMoment B node2971 node2971Labels := rfl
  simpa [nodeValue2971, Sparse.eval] using hc.symm

theorem sound2972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2972 node2972Labels = Sparse.eval nodeValue2972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2972) = mixedMoment B node2972 node2972Labels := rfl
  simpa [nodeValue2972, Sparse.eval] using hc.symm

theorem sound2973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2973 node2973Labels = Sparse.eval nodeValue2973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2973) = mixedMoment B node2973 node2973Labels := rfl
  simpa [nodeValue2973, Sparse.eval] using hc.symm

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2975 node2975Labels = Sparse.eval nodeValue2975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2975) = mixedMoment B node2975 node2975Labels := rfl
  simpa [nodeValue2975, Sparse.eval] using hc.symm

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

theorem sound2977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2977 node2977Labels = Sparse.eval nodeValue2977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2977) = mixedMoment B node2977 node2977Labels := rfl
  simpa [nodeValue2977, Sparse.eval] using hc.symm

theorem sound2978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2978 node2978Labels = Sparse.eval nodeValue2978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2978) = mixedMoment B node2978 node2978Labels := rfl
  simpa [nodeValue2978, Sparse.eval] using hc.symm

theorem sound2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2979 node2979Labels = Sparse.eval nodeValue2979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2979) = mixedMoment B node2979 node2979Labels := rfl
  simpa [nodeValue2979, Sparse.eval] using hc.symm

theorem sound2980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2980 node2980Labels = Sparse.eval nodeValue2980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2980) = mixedMoment B node2980 node2980Labels := rfl
  simpa [nodeValue2980, Sparse.eval] using hc.symm

theorem sound2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2981 node2981Labels = Sparse.eval nodeValue2981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2981) = mixedMoment B node2981 node2981Labels := rfl
  simpa [nodeValue2981, Sparse.eval] using hc.symm

theorem sound2982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2982 node2982Labels = Sparse.eval nodeValue2982 (mixedVector B) := by
  have h := singleton2982 B _hB
  rw [sound216 B _hB _hF] at h
  norm_num [nodeValue2982, nodeValue216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2983 node2983Labels = Sparse.eval nodeValue2983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2983) = mixedMoment B node2983 node2983Labels := rfl
  simpa [nodeValue2983, Sparse.eval] using hc.symm

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

theorem sound2985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2985 node2985Labels = Sparse.eval nodeValue2985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2985) = mixedMoment B node2985 node2985Labels := rfl
  simpa [nodeValue2985, Sparse.eval] using hc.symm

theorem sound2986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2986 node2986Labels = Sparse.eval nodeValue2986 (mixedVector B) := by
  have h := singleton2986 B _hB
  rw [sound304 B _hB _hF] at h
  norm_num [nodeValue2986, nodeValue304, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2987 node2987Labels = Sparse.eval nodeValue2987 (mixedVector B) := by
  have h := singleton2987 B _hB
  rw [sound302 B _hB _hF] at h
  norm_num [nodeValue2987, nodeValue302, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2988 node2988Labels = Sparse.eval nodeValue2988 (mixedVector B) := by
  have h := singleton2988 B _hB
  rw [sound301 B _hB _hF] at h
  norm_num [nodeValue2988, nodeValue301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2989 node2989Labels = Sparse.eval nodeValue2989 (mixedVector B) := by
  have h := singleton2989 B _hB
  rw [sound230 B _hB _hF] at h
  norm_num [nodeValue2989, nodeValue230, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2990 node2990Labels = Sparse.eval nodeValue2990 (mixedVector B) := by
  have h := singleton2990 B _hB
  rw [sound306 B _hB _hF] at h
  norm_num [nodeValue2990, nodeValue306, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2991 node2991Labels = Sparse.eval nodeValue2991 (mixedVector B) := by
  have h := singleton2991 B _hB
  rw [sound307 B _hB _hF] at h
  norm_num [nodeValue2991, nodeValue307, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2992 node2992Labels = Sparse.eval nodeValue2992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2992) = mixedMoment B node2992 node2992Labels := rfl
  simpa [nodeValue2992, Sparse.eval] using hc.symm

theorem sound2993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2993 node2993Labels = Sparse.eval nodeValue2993 (mixedVector B) := by
  simpa only [nodeValue2993, Sparse.eval_nil] using zero2993 B _hB _hF

theorem sound2994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2994 node2994Labels = Sparse.eval nodeValue2994 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2994) = mixedMoment B node2994 node2994Labels := rfl
  simpa [nodeValue2994, Sparse.eval] using hc.symm

theorem sound2995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2995 node2995Labels = Sparse.eval nodeValue2995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2995) = mixedMoment B node2995 node2995Labels := rfl
  simpa [nodeValue2995, Sparse.eval] using hc.symm

theorem sound2996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2996 node2996Labels = Sparse.eval nodeValue2996 (mixedVector B) := by
  have h := singleton2996 B _hB
  rw [sound310 B _hB _hF] at h
  norm_num [nodeValue2996, nodeValue310, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2997 node2997Labels = Sparse.eval nodeValue2997 (mixedVector B) := by
  have h := singleton2997 B _hB
  rw [sound314 B _hB _hF] at h
  norm_num [nodeValue2997, nodeValue314, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2998 node2998Labels = Sparse.eval nodeValue2998 (mixedVector B) := by
  have h := singleton2998 B _hB
  rw [sound312 B _hB _hF] at h
  norm_num [nodeValue2998, nodeValue312, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2999 node2999Labels = Sparse.eval nodeValue2999 (mixedVector B) := by
  simpa only [nodeValue2999, Sparse.eval_nil] using zero2999 B _hB _hF

theorem sound3000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3000 node3000Labels = Sparse.eval nodeValue3000 (mixedVector B) := by
  simpa only [nodeValue3000, Sparse.eval_nil] using zero3000 B _hB _hF

theorem sound3001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3001 node3001Labels = Sparse.eval nodeValue3001 (mixedVector B) := by
  simpa only [nodeValue3001, Sparse.eval_nil] using zero3001 B _hB _hF

theorem sound3002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3002 node3002Labels = Sparse.eval nodeValue3002 (mixedVector B) := by
  simpa only [nodeValue3002, Sparse.eval_nil] using zero3002 B _hB _hF

theorem sound3003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3003 node3003Labels = Sparse.eval nodeValue3003 (mixedVector B) := by
  have h := singleton3003 B _hB
  rw [sound311 B _hB _hF] at h
  norm_num [nodeValue3003, nodeValue311, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3004 node3004Labels = Sparse.eval nodeValue3004 (mixedVector B) := by
  simpa only [nodeValue3004, Sparse.eval_nil] using zero3004 B _hB _hF

theorem sound3005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3005 node3005Labels = Sparse.eval nodeValue3005 (mixedVector B) := by
  have h := singleton3005 B _hB
  rw [sound316 B _hB _hF] at h
  norm_num [nodeValue3005, nodeValue316, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3006 node3006Labels = Sparse.eval nodeValue3006 (mixedVector B) := by
  simpa only [nodeValue3006, Sparse.eval_nil] using zero3006 B _hB _hF

theorem sound3007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3007 node3007Labels = Sparse.eval nodeValue3007 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3007) = mixedMoment B node3007 node3007Labels := rfl
  simpa [nodeValue3007, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
