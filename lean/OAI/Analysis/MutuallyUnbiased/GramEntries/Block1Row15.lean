import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block18
import OAI.Analysis.MutuallyUnbiased.GramRows.Block19
import OAI.Analysis.MutuallyUnbiased.GramRows.Block20
import OAI.Analysis.MutuallyUnbiased.GramRows.Block21
import OAI.Analysis.MutuallyUnbiased.GramRows.Block47
import OAI.Analysis.MutuallyUnbiased.GramRows.Block48
import OAI.Analysis.MutuallyUnbiased.GramRows.Block49
import OAI.Analysis.MutuallyUnbiased.GramRows.Block50
import OAI.Analysis.MutuallyUnbiased.GramRows.Block51

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row700, row701, row702, row703, row704, row705, row3032, row3033, row3034, row712, row713, row714, row715, row716, row717, row3035, row3036, row3037, row3038, row3039, row3040, row3041, row3042, row3043, row3044, row3045, row3046, row3047, row3048, row3049]

theorem entryCheck15_0 : entry15_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_0 k)) := by decide +kernel

theorem rowsSound15_0 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval700 x
  · exact rowEval701 x
  · exact rowEval702 x
  · exact rowEval703 x
  · exact rowEval704 x
  · exact rowEval705 x
  · exact rowEval3032 x
  · exact rowEval3033 x
  · exact rowEval3034 x
  · exact rowEval712 x
  · exact rowEval713 x
  · exact rowEval714 x
  · exact rowEval715 x
  · exact rowEval716 x
  · exact rowEval717 x
  · exact rowEval3035 x
  · exact rowEval3036 x
  · exact rowEval3037 x
  · exact rowEval3038 x
  · exact rowEval3039 x
  · exact rowEval3040 x
  · exact rowEval3041 x
  · exact rowEval3042 x
  · exact rowEval3043 x
  · exact rowEval3044 x
  · exact rowEval3045 x
  · exact rowEval3046 x
  · exact rowEval3047 x
  · exact rowEval3048 x
  · exact rowEval3049 x

theorem entryEval15_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_0 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck15_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_0]

def rows15_1 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row730, row731, row732, row733, row734, row735, row3050, row3051, row3052, row742, row743, row744, row745, row746, row747, row3053, row3054, row3055, row3056, row3057, row3058, row3059, row3060, row3061, row3062, row3063, row3064, row3065, row3066, row3067]

theorem entryCheck15_1 : entry15_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_1 k)) := by decide +kernel

theorem rowsSound15_1 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval730 x
  · exact rowEval731 x
  · exact rowEval732 x
  · exact rowEval733 x
  · exact rowEval734 x
  · exact rowEval735 x
  · exact rowEval3050 x
  · exact rowEval3051 x
  · exact rowEval3052 x
  · exact rowEval742 x
  · exact rowEval743 x
  · exact rowEval744 x
  · exact rowEval745 x
  · exact rowEval746 x
  · exact rowEval747 x
  · exact rowEval3053 x
  · exact rowEval3054 x
  · exact rowEval3055 x
  · exact rowEval3056 x
  · exact rowEval3057 x
  · exact rowEval3058 x
  · exact rowEval3059 x
  · exact rowEval3060 x
  · exact rowEval3061 x
  · exact rowEval3062 x
  · exact rowEval3063 x
  · exact rowEval3064 x
  · exact rowEval3065 x
  · exact rowEval3066 x
  · exact rowEval3067 x

theorem entryEval15_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_1 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck15_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_1]

def rows15_2 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row760, row761, row762, row763, row764, row765, row3068, row3069, row3070, row772, row773, row774, row775, row776, row777, row3071, row3072, row3073, row3074, row3075, row3076, row3077, row3078, row3079, row3080, row3081, row3082, row3083, row3084, row3085]

theorem entryCheck15_2 : entry15_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_2 k)) := by decide +kernel

theorem rowsSound15_2 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval760 x
  · exact rowEval761 x
  · exact rowEval762 x
  · exact rowEval763 x
  · exact rowEval764 x
  · exact rowEval765 x
  · exact rowEval3068 x
  · exact rowEval3069 x
  · exact rowEval3070 x
  · exact rowEval772 x
  · exact rowEval773 x
  · exact rowEval774 x
  · exact rowEval775 x
  · exact rowEval776 x
  · exact rowEval777 x
  · exact rowEval3071 x
  · exact rowEval3072 x
  · exact rowEval3073 x
  · exact rowEval3074 x
  · exact rowEval3075 x
  · exact rowEval3076 x
  · exact rowEval3077 x
  · exact rowEval3078 x
  · exact rowEval3079 x
  · exact rowEval3080 x
  · exact rowEval3081 x
  · exact rowEval3082 x
  · exact rowEval3083 x
  · exact rowEval3084 x
  · exact rowEval3085 x

theorem entryEval15_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_2 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck15_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_2]

def rows15_3 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3086, row3087, row3088, row3089, row3090, row3091, row3092, row3093, row3094, row3095, row3096, row3097, row3098, row3099, row3100, row3101, row3102, row3103, row3104, row3105, row3106, row3107, row3108, row3109, row3110, row3111, row3112, row3113, row3114, row3115]

theorem entryCheck15_3 : entry15_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_3 k)) := by decide +kernel

theorem rowsSound15_3 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval3086 x
  · exact rowEval3087 x
  · exact rowEval3088 x
  · exact rowEval3089 x
  · exact rowEval3090 x
  · exact rowEval3091 x
  · exact rowEval3092 x
  · exact rowEval3093 x
  · exact rowEval3094 x
  · exact rowEval3095 x
  · exact rowEval3096 x
  · exact rowEval3097 x
  · exact rowEval3098 x
  · exact rowEval3099 x
  · exact rowEval3100 x
  · exact rowEval3101 x
  · exact rowEval3102 x
  · exact rowEval3103 x
  · exact rowEval3104 x
  · exact rowEval3105 x
  · exact rowEval3106 x
  · exact rowEval3107 x
  · exact rowEval3108 x
  · exact rowEval3109 x
  · exact rowEval3110 x
  · exact rowEval3111 x
  · exact rowEval3112 x
  · exact rowEval3113 x
  · exact rowEval3114 x
  · exact rowEval3115 x

theorem entryEval15_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_3 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck15_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_3]

def rows15_4 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3116, row3117, row3118, row3119, row3120, row3121, row3122, row3123, row3124, row3125, row3126, row3127, row3128, row3129, row3130, row3131, row3132, row3133, row3134, row3135, row3136, row3137, row3138, row3139, row3140, row3141, row3142, row3143, row3144, row3145]

theorem entryCheck15_4 : entry15_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_4 k)) := by decide +kernel

theorem rowsSound15_4 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval3116 x
  · exact rowEval3117 x
  · exact rowEval3118 x
  · exact rowEval3119 x
  · exact rowEval3120 x
  · exact rowEval3121 x
  · exact rowEval3122 x
  · exact rowEval3123 x
  · exact rowEval3124 x
  · exact rowEval3125 x
  · exact rowEval3126 x
  · exact rowEval3127 x
  · exact rowEval3128 x
  · exact rowEval3129 x
  · exact rowEval3130 x
  · exact rowEval3131 x
  · exact rowEval3132 x
  · exact rowEval3133 x
  · exact rowEval3134 x
  · exact rowEval3135 x
  · exact rowEval3136 x
  · exact rowEval3137 x
  · exact rowEval3138 x
  · exact rowEval3139 x
  · exact rowEval3140 x
  · exact rowEval3141 x
  · exact rowEval3142 x
  · exact rowEval3143 x
  · exact rowEval3144 x
  · exact rowEval3145 x

theorem entryEval15_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_4 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck15_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_4]

def rows15_5 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3146, row3147, row3148, row3149, row3150, row3151, row3152, row3153, row3154, row3155, row3156, row3157, row3158, row3159, row3160, row3161, row3162, row3163, row3164, row3165, row3166, row3167, row3168, row3169, row3170, row3171, row3172, row3173, row3174, row3175]

theorem entryCheck15_5 : entry15_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_5 k)) := by decide +kernel

theorem rowsSound15_5 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval3146 x
  · exact rowEval3147 x
  · exact rowEval3148 x
  · exact rowEval3149 x
  · exact rowEval3150 x
  · exact rowEval3151 x
  · exact rowEval3152 x
  · exact rowEval3153 x
  · exact rowEval3154 x
  · exact rowEval3155 x
  · exact rowEval3156 x
  · exact rowEval3157 x
  · exact rowEval3158 x
  · exact rowEval3159 x
  · exact rowEval3160 x
  · exact rowEval3161 x
  · exact rowEval3162 x
  · exact rowEval3163 x
  · exact rowEval3164 x
  · exact rowEval3165 x
  · exact rowEval3166 x
  · exact rowEval3167 x
  · exact rowEval3168 x
  · exact rowEval3169 x
  · exact rowEval3170 x
  · exact rowEval3171 x
  · exact rowEval3172 x
  · exact rowEval3173 x
  · exact rowEval3174 x
  · exact rowEval3175 x

theorem entryEval15_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_5 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck15_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_5]

def rows15_6 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3176, row3177, row3178, row3179, row3180, row3181, row3182, row3183, row3184, row3185, row3186, row3187, row3188, row3189, row3190, row3191, row3192, row3193, row3194, row3195, row3196, row3197, row3198, row3199, row3200, row3201, row3202, row3203, row3204, row3205]

theorem entryCheck15_6 : entry15_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_6 k)) := by decide +kernel

theorem rowsSound15_6 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval3176 x
  · exact rowEval3177 x
  · exact rowEval3178 x
  · exact rowEval3179 x
  · exact rowEval3180 x
  · exact rowEval3181 x
  · exact rowEval3182 x
  · exact rowEval3183 x
  · exact rowEval3184 x
  · exact rowEval3185 x
  · exact rowEval3186 x
  · exact rowEval3187 x
  · exact rowEval3188 x
  · exact rowEval3189 x
  · exact rowEval3190 x
  · exact rowEval3191 x
  · exact rowEval3192 x
  · exact rowEval3193 x
  · exact rowEval3194 x
  · exact rowEval3195 x
  · exact rowEval3196 x
  · exact rowEval3197 x
  · exact rowEval3198 x
  · exact rowEval3199 x
  · exact rowEval3200 x
  · exact rowEval3201 x
  · exact rowEval3202 x
  · exact rowEval3203 x
  · exact rowEval3204 x
  · exact rowEval3205 x

theorem entryEval15_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_6 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck15_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_6]

def rows15_7 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3206, row3207, row3208, row3209, row3210, row3211, row3212, row3213, row3214, row3215, row3216, row3217, row3218, row3219, row3220, row3221, row3222, row3223, row3224, row3225, row3226, row3227, row3228, row3229, row3230, row3231, row3232, row3233, row3234, row3235]

theorem entryCheck15_7 : entry15_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_7 k)) := by decide +kernel

theorem rowsSound15_7 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval3206 x
  · exact rowEval3207 x
  · exact rowEval3208 x
  · exact rowEval3209 x
  · exact rowEval3210 x
  · exact rowEval3211 x
  · exact rowEval3212 x
  · exact rowEval3213 x
  · exact rowEval3214 x
  · exact rowEval3215 x
  · exact rowEval3216 x
  · exact rowEval3217 x
  · exact rowEval3218 x
  · exact rowEval3219 x
  · exact rowEval3220 x
  · exact rowEval3221 x
  · exact rowEval3222 x
  · exact rowEval3223 x
  · exact rowEval3224 x
  · exact rowEval3225 x
  · exact rowEval3226 x
  · exact rowEval3227 x
  · exact rowEval3228 x
  · exact rowEval3229 x
  · exact rowEval3230 x
  · exact rowEval3231 x
  · exact rowEval3232 x
  · exact rowEval3233 x
  · exact rowEval3234 x
  · exact rowEval3235 x

theorem entryEval15_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_7 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck15_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_7]

def rows15_8 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3236, row3237, row3238, row3239, row3240, row3241, row3242, row3243, row3244, row3245, row3246, row3247, row3248, row3249, row3250, row3251, row3252, row3253, row3254, row3255, row3256, row3257, row3258, row3259, row3260, row3261, row3262, row3263, row3264, row3265]

theorem entryCheck15_8 : entry15_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_8 k)) := by decide +kernel

theorem rowsSound15_8 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval3236 x
  · exact rowEval3237 x
  · exact rowEval3238 x
  · exact rowEval3239 x
  · exact rowEval3240 x
  · exact rowEval3241 x
  · exact rowEval3242 x
  · exact rowEval3243 x
  · exact rowEval3244 x
  · exact rowEval3245 x
  · exact rowEval3246 x
  · exact rowEval3247 x
  · exact rowEval3248 x
  · exact rowEval3249 x
  · exact rowEval3250 x
  · exact rowEval3251 x
  · exact rowEval3252 x
  · exact rowEval3253 x
  · exact rowEval3254 x
  · exact rowEval3255 x
  · exact rowEval3256 x
  · exact rowEval3257 x
  · exact rowEval3258 x
  · exact rowEval3259 x
  · exact rowEval3260 x
  · exact rowEval3261 x
  · exact rowEval3262 x
  · exact rowEval3263 x
  · exact rowEval3264 x
  · exact rowEval3265 x

theorem entryEval15_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_8 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck15_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_8]

def rows15_9 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3266, row3267, row3268, row3269, row3270, row3271, row3272, row3273, row3274, row3275, row3276, row3277, row3278, row3279, row3280, row3281, row3282, row3283, row3284, row3285, row3286, row3287, row3288, row3289, row3290, row3291, row3292, row3293, row3294, row3295]

theorem entryCheck15_9 : entry15_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_9 k)) := by decide +kernel

theorem rowsSound15_9 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval3266 x
  · exact rowEval3267 x
  · exact rowEval3268 x
  · exact rowEval3269 x
  · exact rowEval3270 x
  · exact rowEval3271 x
  · exact rowEval3272 x
  · exact rowEval3273 x
  · exact rowEval3274 x
  · exact rowEval3275 x
  · exact rowEval3276 x
  · exact rowEval3277 x
  · exact rowEval3278 x
  · exact rowEval3279 x
  · exact rowEval3280 x
  · exact rowEval3281 x
  · exact rowEval3282 x
  · exact rowEval3283 x
  · exact rowEval3284 x
  · exact rowEval3285 x
  · exact rowEval3286 x
  · exact rowEval3287 x
  · exact rowEval3288 x
  · exact rowEval3289 x
  · exact rowEval3290 x
  · exact rowEval3291 x
  · exact rowEval3292 x
  · exact rowEval3293 x
  · exact rowEval3294 x
  · exact rowEval3295 x

theorem entryEval15_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_9 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck15_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_9]

def rows15_10 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3296, row3297, row3298, row3299, row3300, row3301, row3302, row3303, row3304, row3305, row3306, row3307, row3308, row3309, row3310, row3311, row3312, row3313, row3314, row3315, row3316, row3317, row3318, row3319, row3320, row3321, row3322, row3323, row3324, row3325]

theorem entryCheck15_10 : entry15_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_10 k)) := by decide +kernel

theorem rowsSound15_10 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval3296 x
  · exact rowEval3297 x
  · exact rowEval3298 x
  · exact rowEval3299 x
  · exact rowEval3300 x
  · exact rowEval3301 x
  · exact rowEval3302 x
  · exact rowEval3303 x
  · exact rowEval3304 x
  · exact rowEval3305 x
  · exact rowEval3306 x
  · exact rowEval3307 x
  · exact rowEval3308 x
  · exact rowEval3309 x
  · exact rowEval3310 x
  · exact rowEval3311 x
  · exact rowEval3312 x
  · exact rowEval3313 x
  · exact rowEval3314 x
  · exact rowEval3315 x
  · exact rowEval3316 x
  · exact rowEval3317 x
  · exact rowEval3318 x
  · exact rowEval3319 x
  · exact rowEval3320 x
  · exact rowEval3321 x
  · exact rowEval3322 x
  · exact rowEval3323 x
  · exact rowEval3324 x
  · exact rowEval3325 x

theorem entryEval15_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_10 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck15_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_10]

def rows15_11 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3326, row3327, row3328, row3329, row3330, row3331, row3332, row3333, row3334, row3335, row3336, row3337, row3338, row3339, row3340, row3341, row3342, row3343, row3344, row3345, row3346, row3347, row3348, row3349, row3350, row3351, row3352, row3353, row3354, row3355]

theorem entryCheck15_11 : entry15_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_11 k)) := by decide +kernel

theorem rowsSound15_11 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval3326 x
  · exact rowEval3327 x
  · exact rowEval3328 x
  · exact rowEval3329 x
  · exact rowEval3330 x
  · exact rowEval3331 x
  · exact rowEval3332 x
  · exact rowEval3333 x
  · exact rowEval3334 x
  · exact rowEval3335 x
  · exact rowEval3336 x
  · exact rowEval3337 x
  · exact rowEval3338 x
  · exact rowEval3339 x
  · exact rowEval3340 x
  · exact rowEval3341 x
  · exact rowEval3342 x
  · exact rowEval3343 x
  · exact rowEval3344 x
  · exact rowEval3345 x
  · exact rowEval3346 x
  · exact rowEval3347 x
  · exact rowEval3348 x
  · exact rowEval3349 x
  · exact rowEval3350 x
  · exact rowEval3351 x
  · exact rowEval3352 x
  · exact rowEval3353 x
  · exact rowEval3354 x
  · exact rowEval3355 x

theorem entryEval15_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_11 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck15_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_11]

def rows15_12 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3356, row3357, row3358, row3359, row3360, row3361, row3362, row3363, row3364, row3365, row3366, row3367, row3368, row3369, row3370, row3371, row3372, row3373, row3374, row3375, row3376, row3377, row3378, row3379, row3380, row3381, row3382, row3383, row3384, row3385]

theorem entryCheck15_12 : entry15_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_12 k)) := by decide +kernel

theorem rowsSound15_12 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval3356 x
  · exact rowEval3357 x
  · exact rowEval3358 x
  · exact rowEval3359 x
  · exact rowEval3360 x
  · exact rowEval3361 x
  · exact rowEval3362 x
  · exact rowEval3363 x
  · exact rowEval3364 x
  · exact rowEval3365 x
  · exact rowEval3366 x
  · exact rowEval3367 x
  · exact rowEval3368 x
  · exact rowEval3369 x
  · exact rowEval3370 x
  · exact rowEval3371 x
  · exact rowEval3372 x
  · exact rowEval3373 x
  · exact rowEval3374 x
  · exact rowEval3375 x
  · exact rowEval3376 x
  · exact rowEval3377 x
  · exact rowEval3378 x
  · exact rowEval3379 x
  · exact rowEval3380 x
  · exact rowEval3381 x
  · exact rowEval3382 x
  · exact rowEval3383 x
  · exact rowEval3384 x
  · exact rowEval3385 x

theorem entryEval15_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_12 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck15_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_12]

def rows15_13 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3386, row3387, row3388, row3389, row3390, row3391, row3392, row3393, row3394, row3395, row3396, row3397, row3398, row3399, row3400, row3401, row3402, row3403, row3404, row3405, row3406, row3407, row3408, row3409, row3410, row3411, row3412, row3413, row3414, row3415]

theorem entryCheck15_13 : entry15_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_13 k)) := by decide +kernel

theorem rowsSound15_13 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval3386 x
  · exact rowEval3387 x
  · exact rowEval3388 x
  · exact rowEval3389 x
  · exact rowEval3390 x
  · exact rowEval3391 x
  · exact rowEval3392 x
  · exact rowEval3393 x
  · exact rowEval3394 x
  · exact rowEval3395 x
  · exact rowEval3396 x
  · exact rowEval3397 x
  · exact rowEval3398 x
  · exact rowEval3399 x
  · exact rowEval3400 x
  · exact rowEval3401 x
  · exact rowEval3402 x
  · exact rowEval3403 x
  · exact rowEval3404 x
  · exact rowEval3405 x
  · exact rowEval3406 x
  · exact rowEval3407 x
  · exact rowEval3408 x
  · exact rowEval3409 x
  · exact rowEval3410 x
  · exact rowEval3411 x
  · exact rowEval3412 x
  · exact rowEval3413 x
  · exact rowEval3414 x
  · exact rowEval3415 x

theorem entryEval15_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_13 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck15_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_13]

def rows15_14 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3416, row3417, row3418, row3419, row3420, row3421, row3422, row3423, row3424, row3425, row3426, row3427, row3428, row3429, row3430, row3431, row3432, row3433, row3434, row3435, row3436, row3437, row3438, row3439, row3440, row3441, row3442, row3443, row3444, row3445]

theorem entryCheck15_14 : entry15_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_14 k)) := by decide +kernel

theorem rowsSound15_14 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval3416 x
  · exact rowEval3417 x
  · exact rowEval3418 x
  · exact rowEval3419 x
  · exact rowEval3420 x
  · exact rowEval3421 x
  · exact rowEval3422 x
  · exact rowEval3423 x
  · exact rowEval3424 x
  · exact rowEval3425 x
  · exact rowEval3426 x
  · exact rowEval3427 x
  · exact rowEval3428 x
  · exact rowEval3429 x
  · exact rowEval3430 x
  · exact rowEval3431 x
  · exact rowEval3432 x
  · exact rowEval3433 x
  · exact rowEval3434 x
  · exact rowEval3435 x
  · exact rowEval3436 x
  · exact rowEval3437 x
  · exact rowEval3438 x
  · exact rowEval3439 x
  · exact rowEval3440 x
  · exact rowEval3441 x
  · exact rowEval3442 x
  · exact rowEval3443 x
  · exact rowEval3444 x
  · exact rowEval3445 x

theorem entryEval15_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_14 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck15_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_14]

def rows15_15 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3446, row3447, row3448, row3449, row3450, row3451, row3452, row3453, row3454, row3455, row3456, row3457, row3458, row3459, row3460, row3461, row3462, row3463, row3464, row3465, row3466, row3467, row3468, row3469, row3470, row3471, row3472, row3473, row3474, row3475]

theorem entryCheck15_15 : entry15_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form15.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form15.terms k).coefficient) (rows15_15 k)) := by decide +kernel

theorem rowsSound15_15 (k : Fin GramFunctions.Block1.form15.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows15_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form15.terms k).tag (GramFunctions.Block1.form15.terms k).charge GramFunctions.Block1.form15) x := by
  fin_cases k
  · exact rowEval3446 x
  · exact rowEval3447 x
  · exact rowEval3448 x
  · exact rowEval3449 x
  · exact rowEval3450 x
  · exact rowEval3451 x
  · exact rowEval3452 x
  · exact rowEval3453 x
  · exact rowEval3454 x
  · exact rowEval3455 x
  · exact rowEval3456 x
  · exact rowEval3457 x
  · exact rowEval3458 x
  · exact rowEval3459 x
  · exact rowEval3460 x
  · exact rowEval3461 x
  · exact rowEval3462 x
  · exact rowEval3463 x
  · exact rowEval3464 x
  · exact rowEval3465 x
  · exact rowEval3466 x
  · exact rowEval3467 x
  · exact rowEval3468 x
  · exact rowEval3469 x
  · exact rowEval3470 x
  · exact rowEval3471 x
  · exact rowEval3472 x
  · exact rowEval3473 x
  · exact rowEval3474 x
  · exact rowEval3475 x

theorem entryEval15_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry15_15 (GramNormalization.eval B) = GramFunctions.Block1.form15.mixedGram GramFunctions.Block1.form15 B := by
  rw [entryCheck15_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form15 GramFunctions.Block1.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound15_15]

end MUB6.Certificate.GramEntries.Block1

end OAI
