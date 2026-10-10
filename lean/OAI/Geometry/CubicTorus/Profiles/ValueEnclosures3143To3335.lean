import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures2921To3142

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e3143 : ℝ := e3138 / e3142
lemma b3143 : Encl e3143 (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3138 b3142 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3144 : ℝ := Real.arcsin e3107
lemma b3144 : Encl e3144 (541780137497 / 1000000000000 : ℝ) (270890068753 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e3107) (a := (136279420271 / 1000000000000 : ℝ)) (b := (136279420273 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (515662015617 / 1000000000000 : ℝ) by norm_num).trans b3107.1
        exact b3107.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3107) (136279420271 / 1000000000000 : ℝ) (136279420273 / 1000000000000 : ℝ) from b3143) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e3145 : ℝ := e59 * e3144
lemma b3145 : Encl e3145 (276307870123 / 1000000000000 : ℝ) (276307870129 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3146 : ℝ := e61 * e3107
lemma b3146 : Encl e3146 (63168596913 / 250000000000 : ℝ) (252674387653 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3107 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3147 : ℝ := e3146 * e3123
lemma b3147 : Encl e3147 (216489416709 / 1000000000000 : ℝ) (216489416711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3146 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3148 : ℝ := e3145 - e3147
lemma b3148 : Encl e3148 (14954613353 / 250000000000 : ℝ) (2990922671 / 50000000000 : ℝ) := by
  exact Encl.sub b3145 b3147 (by norm_num) (by norm_num)

def e3149 : ℝ := e43 * e3123
lemma b3149 : Encl e3149 (428396045047 / 10000000000 : ℝ) (53549505631 / 1250000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3123 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3150 : ℝ := e3107 / e3149
lemma b3150 : Encl e3150 (6018519797 / 500000000000 : ℝ) (2407407919 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3107 b3149 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3151 : ℝ := e3148 - e3150
lemma b3151 : Encl e3151 (47781413817 / 1000000000000 : ℝ) (23890706913 / 500000000000 : ℝ) := by
  exact Encl.sub b3148 b3150 (by norm_num) (by norm_num)

def e3152 : ℝ := e183 - e3151
lemma b3152 : Encl e3152 (236185677843 / 500000000000 : ℝ) (236185677913 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b3151 (by norm_num) (by norm_num)

def e3153 : ℝ := e3152 / e3106
lemma b3153 : Encl e3153 (72896814149 / 250000000000 : ℝ) (291587256683 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3152 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3154 : ℝ := e3136 + e3153
lemma b3154 : Encl e3154 (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact Encl.add b3136 b3153 (by norm_num) (by norm_num)

def e3155 : ℝ := e924 / e3106
lemma b3155 : Encl e3155 (37037037037 / 62500000000 : ℝ) (592592592593 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3156 : ℝ := min e7 e3155
lemma b3156 : Encl e3156 (37037037037 / 62500000000 : ℝ) (592592592593 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b3155 (by norm_num) (by norm_num)

def e3157 : ℝ := e3156 - e5
lemma b3157 : Encl e3157 (-25462962963 / 62500000000 : ℝ) (-407407407407 / 1000000000000 : ℝ) := by
  exact Encl.sub b3156 b5 (by norm_num) (by norm_num)

def e3158 : ℝ := e23 * e3106
lemma b3158 : Encl e3158 (81 / 25 : ℝ) (81 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b3106 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3159 : ℝ := e3158 * e3116
lemma b3159 : Encl e3159 (2101423374667 / 1000000000000 : ℝ) (1050711687337 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3158 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3160 : ℝ := e3159 / e0
lemma b3160 : Encl e3160 (334451917607 / 500000000000 : ℝ) (668903835217 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3159 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3161 : ℝ := e3157 + e3160
lemma b3161 : Encl e3161 (130748213903 / 500000000000 : ℝ) (26149642781 / 100000000000 : ℝ) := by
  exact Encl.add b3157 b3160 (by norm_num) (by norm_num)

def e3162 : ℝ := e23 * e3110
lemma b3162 : Encl e3162 (6561 / 1250 : ℝ) (6561 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b3110 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3163 : ℝ := e3162 * e3116
lemma b3163 : Encl e3163 (42553823337 / 12500000000 : ℝ) (851076466743 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3162 b3116 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3164 : ℝ := e0 + e3163
lemma b3164 : Encl e3164 (6545898520549 / 1000000000000 : ℝ) (3272949260281 / 500000000000 : ℝ) := by
  exact Encl.add b0 b3163 (by norm_num) (by norm_num)

def e3165 : ℝ := Real.sqrt e3164
lemma b3165 : Encl e3165 (127924768131 / 50000000000 : ℝ) (2558495362623 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3164 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3166 : ℝ := e932 * e3165
lemma b3166 : Encl e3166 (1628788735353 / 1000000000000 : ℝ) (814394367679 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b3165 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3167 : ℝ := e3106 ^ 3
lemma b3167 : Encl e3167 (531441 / 125000 : ℝ) (531441 / 125000 : ℝ) := by
  exact Encl.pow b3106 (by norm_num) 3 (by norm_num) (by norm_num)

def e3168 : ℝ := e939 * e3167
lemma b3168 : Encl e3168 (35606547 / 62500000 : ℝ) (35606547 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b3167 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3169 : ℝ := min e3168 e941
lemma b3169 : Encl e3169 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b3168 b941 (by norm_num) (by norm_num)

def e3170 : ℝ := e23 * e3161
lemma b3170 : Encl e3170 (130748213903 / 250000000000 : ℝ) (26149642781 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3161 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3171 : ℝ := e944 * e3169
lemma b3171 : Encl e3171 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b3169 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3172 : ℝ := e3166 ^ 2
lemma b3172 : Encl e3172 (663238186103 / 250000000000 : ℝ) (265295274443 / 100000000000 : ℝ) := by
  exact Encl.pow b3166 (by norm_num) 2 (by norm_num) (by norm_num)

def e3173 : ℝ := e3171 * e3172
lemma b3173 : Encl e3173 (5730377927929 / 1000000000000 : ℝ) (5730377927969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3171 b3172 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3174 : ℝ := e3173 * e3161
lemma b3174 : Encl e3174 (1498473358131 / 1000000000000 : ℝ) (749236679083 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b3173 b3161 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3175 : ℝ := e3174 / e9
lemma b3175 : Encl e3175 (5351690564753 / 1000000000000 : ℝ) (5351690564879 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3174 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3176 : ℝ := e5 + e3175
lemma b3176 : Encl e3176 (6351690564753 / 1000000000000 : ℝ) (6351690564879 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3175 (by norm_num) (by norm_num)

def e3177 : ℝ := Real.sqrt e3176
lemma b3177 : Encl e3177 (1260128025713 / 500000000000 : ℝ) (630064012863 / 250000000000 : ℝ) := by
  exact Encl.sqrt b3176 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3178 : ℝ := e5 + e3177
lemma b3178 : Encl e3178 (1760128025713 / 500000000000 : ℝ) (880064012863 / 250000000000 : ℝ) := by
  exact Encl.add b5 b3177 (by norm_num) (by norm_num)

def e3179 : ℝ := e3170 / e3178
lemma b3179 : Encl e3179 (5942668351 / 40000000000 : ℝ) (7428335439 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b3170 b3178 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3180 : ℝ := e3169 * e954
lemma b3180 : Encl e3180 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b3169 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3181 : ℝ := e3161 - e3179
lemma b3181 : Encl e3181 (56464859513 / 500000000000 : ℝ) (22585943807 / 200000000000 : ℝ) := by
  exact Encl.sub b3161 b3179 (by norm_num) (by norm_num)

def e3182 : ℝ := e3181 / e3166
lemma b3182 : Encl e3182 (34666779237 / 500000000000 : ℝ) (69333558481 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3181 b3166 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3183 : ℝ := e3182 ^ 2
lemma b3183 : Encl e3183 (480714233 / 100000000000 : ℝ) (1201785583 / 250000000000 : ℝ) := by
  exact Encl.pow b3182 (by norm_num) 2 (by norm_num) (by norm_num)

def e3184 : ℝ := e9 * e3183
lemma b3184 : Encl e3184 (336499963 / 250000000000 : ℝ) (1345999853 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3183 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3185 : ℝ := e3179 ^ 3
lemma b3185 : Encl e3185 (3279174343 / 1000000000000 : ℝ) (409896793 / 125000000000 : ℝ) := by
  exact Encl.pow b3179 (by norm_num) 3 (by norm_num) (by norm_num)

def e3186 : ℝ := e3169 * e3185
lemma b3186 : Encl e3186 (1180502763 / 1000000000000 : ℝ) (295125691 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3169 b3185 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3187 : ℝ := e3184 + e3186
lemma b3187 : Encl e3187 (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  exact Encl.add b3184 b3186 (by norm_num) (by norm_num)

def e3188 : ℝ := min e3180 e3187
lemma b3188 : Encl e3188 (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  exact Encl.min b3180 b3187 (by norm_num) (by norm_num)

def e3189 : ℝ := (17 / 10 : ℝ)
lemma b3189 : Encl e3189 (17 / 10 : ℝ) (17 / 10 : ℝ) := by
  exact Encl.exact (17 / 10 : ℝ)

def e3190 : ℝ := e3189 / e0
lemma b3190 : Encl e3190 (33820425407 / 62500000000 : ℝ) (541126806513 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3189 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3191 : ℝ := e8 * e3189
lemma b3191 : Encl e3191 (833 / 500 : ℝ) (833 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3189 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3192 : ℝ := e3191 / e0
lemma b3192 : Encl e3192 (265152135191 / 500000000000 : ℝ) (530304270383 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3191 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3193 : ℝ := e3189 ^ 2
lemma b3193 : Encl e3193 (289 / 100 : ℝ) (289 / 100 : ℝ) := by
  exact Encl.pow b3189 (by norm_num) 2 (by norm_num) (by norm_num)

def e3194 : ℝ := e17 * e3193
lemma b3194 : Encl e3194 (289 / 25 : ℝ) (289 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b3193 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3195 : ℝ := e3194 / e0
lemma b3195 : Encl e3195 (919915571071 / 250000000000 : ℝ) (735932456857 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3194 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3196 : ℝ := e5 + e3195
lemma b3196 : Encl e3196 (1169915571071 / 250000000000 : ℝ) (935932456857 / 200000000000 : ℝ) := by
  exact Encl.add b5 b3195 (by norm_num) (by norm_num)

def e3197 : ℝ := Real.sqrt e3196
lemma b3197 : Encl e3197 (2163252709297 / 1000000000000 : ℝ) (1081626354649 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3196 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3198 : ℝ := e5 + e3197
lemma b3198 : Encl e3198 (3163252709297 / 1000000000000 : ℝ) (1581626354649 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3197 (by norm_num) (by norm_num)

def e3199 : ℝ := e23 / e3198
lemma b3199 : Encl e3199 (316130291159 / 500000000000 : ℝ) (632260582319 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3198 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3200 : ℝ := e9 * e3199
lemma b3200 : Encl e3200 (177032963049 / 1000000000000 : ℝ) (3540659261 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3199 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3201 : ℝ := e3192 + e3200
lemma b3201 : Encl e3201 (707337233431 / 1000000000000 : ℝ) (707337233433 / 1000000000000 : ℝ) := by
  exact Encl.add b3192 b3200 (by norm_num) (by norm_num)

def e3202 : ℝ := e3201 - e5
lemma b3202 : Encl e3202 (-292662766569 / 1000000000000 : ℝ) (-292662766567 / 1000000000000 : ℝ) := by
  exact Encl.sub b3201 b5 (by norm_num) (by norm_num)

def e3203 : ℝ := e0 / e3193
lemma b3203 : Encl e3203 (543528140759 / 500000000000 : ℝ) (1087056281519 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3193 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3204 : ℝ := e3190 ^ 2
lemma b3204 : Encl e3204 (11712728829 / 40000000000 : ℝ) (292818220727 / 1000000000000 : ℝ) := by
  exact Encl.pow b3190 (by norm_num) 2 (by norm_num) (by norm_num)

def e3205 : ℝ := e5 - e3204
lemma b3205 : Encl e3205 (707181779273 / 1000000000000 : ℝ) (28287271171 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b3204 (by norm_num) (by norm_num)

def e3206 : ℝ := Real.sqrt e3205
lemma b3206 : Encl e3206 (4204705041 / 5000000000 : ℝ) (420470504101 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3205 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3207 : ℝ := e29 - e3206
lemma b3207 : Encl e3207 (-5446073173 / 31250000000 : ℝ) (-174274341533 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b3206 (by norm_num) (by norm_num)

def e3208 : ℝ := e3206 ^ 3
lemma b3208 : Encl e3208 (297349079221 / 500000000000 : ℝ) (594698158447 / 1000000000000 : ℝ) := by
  exact Encl.pow b3206 (by norm_num) 3 (by norm_num) (by norm_num)

def e3209 : ℝ := e3208 / e35
lemma b3209 : Encl e3209 (4955817987 / 25000000000 : ℝ) (198232719483 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3208 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3210 : ℝ := e3207 + e3209
lemma b3210 : Encl e3210 (2994797243 / 125000000000 : ℝ) (479167559 / 20000000000 : ℝ) := by
  exact Encl.add b3207 b3209 (by norm_num) (by norm_num)

def e3211 : ℝ := e8 * e3210
lemma b3211 : Encl e3211 (4695842077 / 200000000000 : ℝ) (23479210391 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3210 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3212 : ℝ := e3204 / e3206
lemma b3212 : Encl e3212 (348203046193 / 1000000000000 : ℝ) (348203046197 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3204 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3213 : ℝ := e3212 - e23
lemma b3213 : Encl e3213 (-1651796953807 / 1000000000000 : ℝ) (-1651796953803 / 1000000000000 : ℝ) := by
  exact Encl.sub b3212 b23 (by norm_num) (by norm_num)

def e3214 : ℝ := e23 * e3206
lemma b3214 : Encl e3214 (4204705041 / 2500000000 : ℝ) (420470504101 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3215 : ℝ := e3213 + e3214
lemma b3215 : Encl e3215 (30085062593 / 1000000000000 : ℝ) (30085062601 / 1000000000000 : ℝ) := by
  exact Encl.add b3213 b3214 (by norm_num) (by norm_num)

def e3216 : ℝ := e3215 / e43
lemma b3216 : Encl e3216 (601701251 / 1000000000000 : ℝ) (601701253 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3215 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3217 : ℝ := e3211 - e3216
lemma b3217 : Encl e3217 (5719377283 / 250000000000 : ℝ) (1143875457 / 50000000000 : ℝ) := by
  exact Encl.sub b3211 b3216 (by norm_num) (by norm_num)

def e3218 : ℝ := e3203 * e3217
lemma b3218 : Encl e3218 (24869140007 / 1000000000000 : ℝ) (24869140017 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3203 b3217 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3219 : ℝ := e3202 + e3218
lemma b3219 : Encl e3219 (-133896813281 / 500000000000 : ℝ) (-5355872531 / 20000000000 : ℝ) := by
  exact Encl.add b3202 b3218 (by norm_num) (by norm_num)

def e3220 : ℝ := e5 + e3206
lemma b3220 : Encl e3220 (9204705041 / 5000000000 : ℝ) (920470504101 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3206 (by norm_num) (by norm_num)

def e3221 : ℝ := e3190 / e3220
lemma b3221 : Encl e3221 (73485082371 / 250000000000 : ℝ) (146970164743 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3190 b3220 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3222 : ℝ := e3221 ^ 2
lemma b3222 : Encl e3222 (86400917297 / 1000000000000 : ℝ) (86400917299 / 1000000000000 : ℝ) := by
  exact Encl.pow b3221 (by norm_num) 2 (by norm_num) (by norm_num)

def e3223 : ℝ := e5 + e3222
lemma b3223 : Encl e3223 (1086400917297 / 1000000000000 : ℝ) (1086400917299 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3222 (by norm_num) (by norm_num)

def e3224 : ℝ := Real.sqrt e3223
lemma b3224 : Encl e3224 (32572049303 / 31250000000 : ℝ) (521152788849 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3223 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3225 : ℝ := e5 + e3224
lemma b3225 : Encl e3225 (63822049303 / 31250000000 : ℝ) (1021152788849 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3224 (by norm_num) (by norm_num)

def e3226 : ℝ := e3221 / e3225
lemma b3226 : Encl e3226 (143925734079 / 1000000000000 : ℝ) (143925734081 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3221 b3225 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3227 : ℝ := Real.arcsin e3190
lemma b3227 : Encl e3227 (571776467901 / 1000000000000 : ℝ) (57177646791 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e3190) (a := (143925734079 / 1000000000000 : ℝ)) (b := (143925734081 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (33820425407 / 62500000000 : ℝ) by norm_num).trans b3190.1
        exact b3190.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3190) (143925734079 / 1000000000000 : ℝ) (143925734081 / 1000000000000 : ℝ) from b3226) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e3228 : ℝ := e59 * e3227
lemma b3228 : Encl e3228 (291605998629 / 1000000000000 : ℝ) (58321199727 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3227 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3229 : ℝ := e61 * e3190
lemma b3229 : Encl e3229 (26515213519 / 100000000000 : ℝ) (33144016899 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3230 : ℝ := e3229 * e3206
lemma b3230 : Encl e3230 (222977303893 / 1000000000000 : ℝ) (27872162987 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b3229 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3231 : ℝ := e3228 - e3230
lemma b3231 : Encl e3231 (68628694733 / 1000000000000 : ℝ) (34314347371 / 500000000000 : ℝ) := by
  exact Encl.sub b3228 b3230 (by norm_num) (by norm_num)

def e3232 : ℝ := e43 * e3206
lemma b3232 : Encl e3232 (4204705041 / 100000000 : ℝ) (420470504101 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3206 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3233 : ℝ := e3190 / e3232
lemma b3233 : Encl e3233 (3217388623 / 250000000000 : ℝ) (12869554493 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3190 b3232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3234 : ℝ := e3231 - e3233
lemma b3234 : Encl e3234 (696989253 / 12500000000 : ℝ) (223036561 / 4000000000 : ℝ) := by
  exact Encl.sub b3231 b3233 (by norm_num) (by norm_num)

def e3235 : ℝ := e183 - e3234
lemma b3235 : Encl e3235 (232196814631 / 500000000000 : ℝ) (464393629403 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3234 (by norm_num) (by norm_num)

def e3236 : ℝ := e3235 / e3189
lemma b3236 : Encl e3236 (54634544619 / 200000000000 : ℝ) (273172723179 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3235 b3189 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3237 : ℝ := e3219 + e3236
lemma b3237 : Encl e3237 (5379096533 / 1000000000000 : ℝ) (5379096629 / 1000000000000 : ℝ) := by
  exact Encl.add b3219 b3236 (by norm_num) (by norm_num)

def e3238 : ℝ := (19 / 10 : ℝ)
lemma b3238 : Encl e3238 (19 / 10 : ℝ) (19 / 10 : ℝ) := by
  exact Encl.exact (19 / 10 : ℝ)

def e3239 : ℝ := e3238 / e0
lemma b3239 : Encl e3239 (604788783749 / 1000000000000 : ℝ) (483831027 / 800000000 : ℝ) := by
  exact Encl.div_nonneg b3238 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3240 : ℝ := e8 * e3238
lemma b3240 : Encl e3240 (931 / 500 : ℝ) (931 / 500 : ℝ) := by
  exact Encl.mul_nonneg b8 b3238 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3241 : ℝ := e3240 / e0
lemma b3241 : Encl e3241 (296346504037 / 500000000000 : ℝ) (23707720323 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b3240 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3242 : ℝ := e3238 ^ 2
lemma b3242 : Encl e3242 (361 / 100 : ℝ) (361 / 100 : ℝ) := by
  exact Encl.pow b3238 (by norm_num) 2 (by norm_num) (by norm_num)

def e3243 : ℝ := e17 * e3242
lemma b3243 : Encl e3243 (361 / 25 : ℝ) (361 / 25 : ℝ) := by
  exact Encl.mul_nonneg b17 b3242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3244 : ℝ := e3243 / e0
lemma b3244 : Encl e3244 (4596394756493 / 1000000000000 : ℝ) (2298197378247 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3243 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3245 : ℝ := e5 + e3244
lemma b3245 : Encl e3245 (5596394756493 / 1000000000000 : ℝ) (2798197378247 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3244 (by norm_num) (by norm_num)

def e3246 : ℝ := Real.sqrt e3245
lemma b3246 : Encl e3246 (591417510969 / 250000000000 : ℝ) (2365670043877 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b3245 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3247 : ℝ := e5 + e3246
lemma b3247 : Encl e3247 (841417510969 / 250000000000 : ℝ) (3365670043877 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b3246 (by norm_num) (by norm_num)

def e3248 : ℝ := e23 / e3247
lemma b3248 : Encl e3248 (594235315383 / 1000000000000 : ℝ) (74279414423 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3247 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3249 : ℝ := e9 * e3248
lemma b3249 : Encl e3249 (166385888307 / 1000000000000 : ℝ) (41596472077 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3248 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3250 : ℝ := e3241 + e3249
lemma b3250 : Encl e3250 (759078896381 / 1000000000000 : ℝ) (759078896383 / 1000000000000 : ℝ) := by
  exact Encl.add b3241 b3249 (by norm_num) (by norm_num)

def e3251 : ℝ := e3250 - e5
lemma b3251 : Encl e3251 (-240921103619 / 1000000000000 : ℝ) (-240921103617 / 1000000000000 : ℝ) := by
  exact Encl.sub b3250 b5 (by norm_num) (by norm_num)

def e3252 : ℝ := e0 / e3242
lemma b3252 : Encl e3252 (435123636231 / 500000000000 : ℝ) (870247272463 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3253 : ℝ := e3239 ^ 2
lemma b3253 : Encl e3253 (91442368237 / 250000000000 : ℝ) (7315389459 / 20000000000 : ℝ) := by
  exact Encl.pow b3239 (by norm_num) 2 (by norm_num) (by norm_num)

def e3254 : ℝ := e5 - e3253
lemma b3254 : Encl e3254 (12684610541 / 20000000000 : ℝ) (158557631763 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b3253 (by norm_num) (by norm_num)

def e3255 : ℝ := Real.sqrt e3254
lemma b3255 : Encl e3255 (796385915903 / 1000000000000 : ℝ) (398192957953 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3254 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3256 : ℝ := e29 - e3255
lemma b3256 : Encl e3256 (-3242981231 / 25000000000 : ℝ) (-32429812309 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b3255 (by norm_num) (by norm_num)

def e3257 : ℝ := e3255 ^ 3
lemma b3257 : Encl e3257 (505092259177 / 1000000000000 : ℝ) (505092259183 / 1000000000000 : ℝ) := by
  exact Encl.pow b3255 (by norm_num) 3 (by norm_num) (by norm_num)

def e3258 : ℝ := e3257 / e35
lemma b3258 : Encl e3258 (21045510799 / 125000000000 : ℝ) (33672817279 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b3257 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3259 : ℝ := e3256 + e3258
lemma b3259 : Encl e3259 (1207651161 / 31250000000 : ℝ) (38644837159 / 1000000000000 : ℝ) := by
  exact Encl.add b3256 b3258 (by norm_num) (by norm_num)

def e3260 : ℝ := e8 * e3259
lemma b3260 : Encl e3260 (4733992551 / 125000000000 : ℝ) (591749069 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3259 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3261 : ℝ := e3253 / e3255
lemma b3261 : Encl e3261 (459286717209 / 1000000000000 : ℝ) (229643358607 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3253 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3262 : ℝ := e3261 - e23
lemma b3262 : Encl e3262 (-1540713282791 / 1000000000000 : ℝ) (-770356641393 / 500000000000 : ℝ) := by
  exact Encl.sub b3261 b23 (by norm_num) (by norm_num)

def e3263 : ℝ := e23 * e3255
lemma b3263 : Encl e3263 (796385915903 / 500000000000 : ℝ) (398192957953 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3264 : ℝ := e3262 + e3263
lemma b3264 : Encl e3264 (10411709803 / 200000000000 : ℝ) (26029274513 / 500000000000 : ℝ) := by
  exact Encl.add b3262 b3263 (by norm_num) (by norm_num)

def e3265 : ℝ := e3264 / e43
lemma b3265 : Encl e3265 (52058549 / 50000000000 : ℝ) (1041170981 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3264 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3266 : ℝ := e3260 - e3265
lemma b3266 : Encl e3266 (36830769427 / 1000000000000 : ℝ) (9207692359 / 250000000000 : ℝ) := by
  exact Encl.sub b3260 b3265 (by norm_num) (by norm_num)

def e3267 : ℝ := e3252 * e3266
lemma b3267 : Encl e3267 (8012969159 / 250000000000 : ℝ) (6410375329 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b3252 b3266 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3268 : ℝ := e3251 + e3267
lemma b3268 : Encl e3268 (-208869226983 / 1000000000000 : ℝ) (-52217306743 / 250000000000 : ℝ) := by
  exact Encl.add b3251 b3267 (by norm_num) (by norm_num)

def e3269 : ℝ := e5 + e3255
lemma b3269 : Encl e3269 (1796385915903 / 1000000000000 : ℝ) (898192957953 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3255 (by norm_num) (by norm_num)

def e3270 : ℝ := e3239 / e3269
lemma b3270 : Encl e3270 (67333948501 / 200000000000 : ℝ) (336669742507 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3239 b3269 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3271 : ℝ := e3270 ^ 2
lemma b3271 : Encl e3271 (56673257759 / 500000000000 : ℝ) (354207861 / 3125000000 : ℝ) := by
  exact Encl.pow b3270 (by norm_num) 2 (by norm_num) (by norm_num)

def e3272 : ℝ := e5 + e3271
lemma b3272 : Encl e3272 (556673257759 / 500000000000 : ℝ) (3479207861 / 3125000000 : ℝ) := by
  exact Encl.add b5 b3271 (by norm_num) (by norm_num)

def e3273 : ℝ := Real.sqrt e3272
lemma b3273 : Encl e3273 (52757618301 / 50000000000 : ℝ) (527576183011 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3272 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3274 : ℝ := e5 + e3273
lemma b3274 : Encl e3274 (102757618301 / 50000000000 : ℝ) (1027576183011 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3273 (by norm_num) (by norm_num)

def e3275 : ℝ := e3270 / e3274
lemma b3275 : Encl e3275 (16381741231 / 100000000000 : ℝ) (20477176539 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3270 b3274 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3276 : ℝ := Real.arcsin e3239
lemma b3276 : Encl e3276 (649500622237 / 1000000000000 : ℝ) (324750311123 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e3239) (a := (16381741231 / 100000000000 : ℝ)) (b := (20477176539 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (604788783749 / 1000000000000 : ℝ) by norm_num).trans b3239.1
        exact b3239.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3239) (16381741231 / 100000000000 : ℝ) (20477176539 / 125000000000 : ℝ) from b3275) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e3277 : ℝ := e59 * e3276
lemma b3277 : Encl e3277 (16562265867 / 50000000000 : ℝ) (165622658673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3276 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3278 : ℝ := e61 * e3239
lemma b3278 : Encl e3278 (296346504037 / 1000000000000 : ℝ) (148173252019 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3239 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3279 : ℝ := e3278 * e3255
lemma b3279 : Encl e3279 (118003091021 / 500000000000 : ℝ) (59001545511 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b3278 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3280 : ℝ := e3277 - e3279
lemma b3280 : Encl e3280 (1488111489 / 15625000000 : ℝ) (11904891913 / 125000000000 : ℝ) := by
  exact Encl.sub b3277 b3279 (by norm_num) (by norm_num)

def e3281 : ℝ := e43 * e3255
lemma b3281 : Encl e3281 (796385915903 / 20000000000 : ℝ) (398192957953 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3255 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3282 : ℝ := e3239 / e3281
lemma b3282 : Encl e3282 (15188334491 / 1000000000000 : ℝ) (3797083623 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3239 b3281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3283 : ℝ := e3280 - e3282
lemma b3283 : Encl e3283 (20012700201 / 250000000000 : ℝ) (80050800813 / 1000000000000 : ℝ) := by
  exact Encl.sub b3280 b3282 (by norm_num) (by norm_num)

def e3284 : ℝ := e183 - e3283
lemma b3284 : Encl e3284 (440101968699 / 1000000000000 : ℝ) (440101968839 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b3283 (by norm_num) (by norm_num)

def e3285 : ℝ := e3284 / e3238
lemma b3285 : Encl e3285 (3619259611 / 15625000000 : ℝ) (231632615179 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b3284 b3238 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3286 : ℝ := e3268 + e3285
lemma b3286 : Encl e3286 (22763388121 / 1000000000000 : ℝ) (22763388207 / 1000000000000 : ℝ) := by
  exact Encl.add b3268 b3285 (by norm_num) (by norm_num)

def e3287 : ℝ := (9 / 4 : ℝ)
lemma b3287 : Encl e3287 (9 / 4 : ℝ) (9 / 4 : ℝ) := by
  exact Encl.exact (9 / 4 : ℝ)

def e3288 : ℝ := e3287 / e0
lemma b3288 : Encl e3288 (716197243913 / 1000000000000 : ℝ) (358098621957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3287 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3289 : ℝ := e8 * e3287
lemma b3289 : Encl e3289 (441 / 200 : ℝ) (441 / 200 : ℝ) := by
  exact Encl.mul_nonneg b8 b3287 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3290 : ℝ := e3289 / e0
lemma b3290 : Encl e3290 (140374659807 / 200000000000 : ℝ) (175468324759 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b3289 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3291 : ℝ := e3287 ^ 2
lemma b3291 : Encl e3291 (81 / 16 : ℝ) (81 / 16 : ℝ) := by
  exact Encl.pow b3287 (by norm_num) 2 (by norm_num) (by norm_num)

def e3292 : ℝ := e17 * e3291
lemma b3292 : Encl e3292 (81 / 4 : ℝ) (81 / 4 : ℝ) := by
  exact Encl.mul_nonneg b17 b3291 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3293 : ℝ := e3292 / e0
lemma b3293 : Encl e3293 (6445775195221 / 1000000000000 : ℝ) (3222887597611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3292 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3294 : ℝ := e5 + e3293
lemma b3294 : Encl e3294 (7445775195221 / 1000000000000 : ℝ) (3722887597611 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3293 (by norm_num) (by norm_num)

def e3295 : ℝ := Real.sqrt e3294
lemma b3295 : Encl e3295 (682173694671 / 250000000000 : ℝ) (545738955737 / 200000000000 : ℝ) := by
  exact Encl.sqrt b3294 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3296 : ℝ := e5 + e3295
lemma b3296 : Encl e3296 (932173694671 / 250000000000 : ℝ) (745738955737 / 200000000000 : ℝ) := by
  exact Encl.add b5 b3295 (by norm_num) (by norm_num)

def e3297 : ℝ := e23 / e3296
lemma b3297 : Encl e3297 (134095180667 / 250000000000 : ℝ) (536380722669 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b3296 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3298 : ℝ := e9 * e3297
lemma b3298 : Encl e3298 (150186602347 / 1000000000000 : ℝ) (37546650587 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b3297 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3299 : ℝ := e3290 + e3298
lemma b3299 : Encl e3299 (426029950691 / 500000000000 : ℝ) (106507487673 / 125000000000 : ℝ) := by
  exact Encl.add b3290 b3298 (by norm_num) (by norm_num)

def e3300 : ℝ := e3299 - e5
lemma b3300 : Encl e3300 (-73970049309 / 500000000000 : ℝ) (-18492512327 / 125000000000 : ℝ) := by
  exact Encl.sub b3299 b5 (by norm_num) (by norm_num)

def e3301 : ℝ := e0 / e3291
lemma b3301 : Encl e3301 (31028075591 / 50000000000 : ℝ) (620561511821 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b3291 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3302 : ℝ := e3288 ^ 2
lemma b3302 : Encl e3302 (128234623047 / 250000000000 : ℝ) (512938492191 / 1000000000000 : ℝ) := by
  exact Encl.pow b3288 (by norm_num) 2 (by norm_num) (by norm_num)

def e3303 : ℝ := e5 - e3302
lemma b3303 : Encl e3303 (487061507809 / 1000000000000 : ℝ) (121765376953 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b3302 (by norm_num) (by norm_num)

def e3304 : ℝ := Real.sqrt e3303
lemma b3304 : Encl e3304 (139579584153 / 200000000000 : ℝ) (2726163753 / 3906250000 : ℝ) := by
  exact Encl.sqrt b3303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3305 : ℝ := e29 - e3304
lemma b3305 : Encl e3305 (-15615627051 / 500000000000 : ℝ) (-15615627049 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b3304 (by norm_num) (by norm_num)

def e3306 : ℝ := e3304 ^ 3
lemma b3306 : Encl e3306 (339919213583 / 1000000000000 : ℝ) (339919213589 / 1000000000000 : ℝ) := by
  exact Encl.pow b3304 (by norm_num) 3 (by norm_num) (by norm_num)

def e3307 : ℝ := e3306 / e35
lemma b3307 : Encl e3307 (113306404527 / 1000000000000 : ℝ) (11330640453 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b3306 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3308 : ℝ := e3305 + e3307
lemma b3308 : Encl e3308 (3283006017 / 40000000000 : ℝ) (2564848451 / 31250000000 : ℝ) := by
  exact Encl.add b3305 b3307 (by norm_num) (by norm_num)

def e3309 : ℝ := e8 * e3308
lemma b3309 : Encl e3309 (10054205927 / 125000000000 : ℝ) (1256775741 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b3308 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3310 : ℝ := e3302 / e3304
lemma b3310 : Encl e3310 (367488193419 / 500000000000 : ℝ) (367488193423 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3302 b3304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3311 : ℝ := e3310 - e23
lemma b3311 : Encl e3311 (-632511806581 / 500000000000 : ℝ) (-632511806577 / 500000000000 : ℝ) := by
  exact Encl.sub b3310 b23 (by norm_num) (by norm_num)

def e3312 : ℝ := e23 * e3304
lemma b3312 : Encl e3312 (139579584153 / 100000000000 : ℝ) (2726163753 / 1953125000 : ℝ) := by
  exact Encl.mul_nonneg b23 b3304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3313 : ℝ := e3311 + e3312
lemma b3313 : Encl e3313 (8173264273 / 62500000000 : ℝ) (65386114191 / 500000000000 : ℝ) := by
  exact Encl.add b3311 b3312 (by norm_num) (by norm_num)

def e3314 : ℝ := e3313 / e43
lemma b3314 : Encl e3314 (2615444567 / 1000000000000 : ℝ) (326930571 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b3313 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3315 : ℝ := e3309 - e3314
lemma b3315 : Encl e3315 (2431818839 / 31250000000 : ℝ) (77818202857 / 1000000000000 : ℝ) := by
  exact Encl.sub b3309 b3314 (by norm_num) (by norm_num)

def e3316 : ℝ := e3301 * e3315
lemma b3316 : Encl e3316 (24145490803 / 500000000000 : ℝ) (48290981613 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b3301 b3315 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3317 : ℝ := e3300 + e3316
lemma b3317 : Encl e3317 (-24912279253 / 250000000000 : ℝ) (-99649117003 / 1000000000000 : ℝ) := by
  exact Encl.add b3300 b3316 (by norm_num) (by norm_num)

def e3318 : ℝ := e5 + e3304
lemma b3318 : Encl e3318 (339579584153 / 200000000000 : ℝ) (6632413753 / 3906250000 : ℝ) := by
  exact Encl.add b5 b3304 (by norm_num) (by norm_num)

def e3319 : ℝ := e3288 / e3318
lemma b3319 : Encl e3319 (210907038389 / 500000000000 : ℝ) (21090703839 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b3288 b3318 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3320 : ℝ := e3319 ^ 2
lemma b3320 : Encl e3320 (22240889421 / 125000000000 : ℝ) (17792711537 / 100000000000 : ℝ) := by
  exact Encl.pow b3319 (by norm_num) 2 (by norm_num) (by norm_num)

def e3321 : ℝ := e5 + e3320
lemma b3321 : Encl e3321 (147240889421 / 125000000000 : ℝ) (117792711537 / 100000000000 : ℝ) := by
  exact Encl.add b5 b3320 (by norm_num) (by norm_num)

def e3322 : ℝ := Real.sqrt e3321
lemma b3322 : Encl e3322 (27133087681 / 25000000000 : ℝ) (542661753621 / 500000000000 : ℝ) := by
  exact Encl.sqrt b3321 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3323 : ℝ := e5 + e3322
lemma b3323 : Encl e3323 (52133087681 / 25000000000 : ℝ) (1042661753621 / 500000000000 : ℝ) := by
  exact Encl.add b5 b3322 (by norm_num) (by norm_num)

def e3324 : ℝ := e3319 / e3323
lemma b3324 : Encl e3324 (50569381119 / 250000000000 : ℝ) (101138762239 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b3319 b3323 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3325 : ℝ := Real.arcsin e3288
lemma b3325 : Encl e3325 (798338099991 / 1000000000000 : ℝ) (7983381 / 10000000 : ℝ) := by
  apply Encl.arcsin (z := e3288) (a := (50569381119 / 250000000000 : ℝ)) (b := (101138762239 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (716197243913 / 1000000000000 : ℝ) by norm_num).trans b3288.1
        exact b3288.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e3288) (50569381119 / 250000000000 : ℝ) (101138762239 / 500000000000 : ℝ) from b3324) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e3326 : ℝ := e59 * e3325
lemma b3326 : Encl e3326 (81430486199 / 200000000000 : ℝ) (407152431 / 1000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b3325 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3327 : ℝ := e61 * e3288
lemma b3327 : Encl e3327 (350936649517 / 1000000000000 : ℝ) (175468324759 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b3288 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3328 : ℝ := e3327 * e3304
lemma b3328 : Encl e3328 (122458979009 / 500000000000 : ℝ) (12245897901 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b3327 b3304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3329 : ℝ := e3326 - e3328
lemma b3329 : Encl e3329 (6489378919 / 40000000000 : ℝ) (81117236491 / 500000000000 : ℝ) := by
  exact Encl.sub b3326 b3328 (by norm_num) (by norm_num)

def e3330 : ℝ := e43 * e3304
lemma b3330 : Encl e3330 (139579584153 / 4000000000 : ℝ) (2726163753 / 78125000 : ℝ) := by
  exact Encl.mul_nonneg b43 b3304 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3331 : ℝ := e3288 / e3330
lemma b3331 : Encl e3331 (20524412599 / 1000000000000 : ℝ) (102622063 / 5000000000 : ℝ) := by
  exact Encl.div_nonneg b3288 b3330 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3332 : ℝ := e3329 - e3331
lemma b3332 : Encl e3332 (1133680483 / 8000000000 : ℝ) (141710060383 / 1000000000000 : ℝ) := by
  exact Encl.sub b3329 b3331 (by norm_num) (by norm_num)

def e3333 : ℝ := e183 - e3332
lemma b3333 : Encl e3333 (378442709129 / 1000000000000 : ℝ) (94610677317 / 250000000000 : ℝ) := by
  exact Encl.sub b183 b3332 (by norm_num) (by norm_num)

def e3334 : ℝ := e3333 / e3287
lemma b3334 : Encl e3334 (42049189903 / 250000000000 : ℝ) (6727870387 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b3333 b3287 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3335 : ℝ := e3317 + e3334
lemma b3335 : Encl e3335 (342738213 / 5000000000 : ℝ) (4284227667 / 62500000000 : ℝ) := by
  exact Encl.add b3317 b3334 (by norm_num) (by norm_num)

lemma baseline_enclosure_64 : Encl (twoChordBaseline (16 / 25 : ℝ)) (6874889409 / 500000000000 : ℝ) (13749779263 / 1000000000000 : ℝ) := by
  exact b189

lemma baseline_enclosure_74 : Encl (twoChordBaseline (37 / 50 : ℝ)) (383669089 / 40000000000 : ℝ) (9591727677 / 1000000000000 : ℝ) := by
  exact b336

lemma baseline_enclosure_84 : Encl (twoChordBaseline (21 / 25 : ℝ)) (146341961 / 25000000000 : ℝ) (46829431 / 8000000000 : ℝ) := by
  exact b483

lemma baseline_enclosure_92 : Encl (twoChordBaseline (23 / 25 : ℝ)) (334736981 / 100000000000 : ℝ) (669474053 / 200000000000 : ℝ) := by
  exact b630

lemma baseline_enclosure_98 : Encl (twoChordBaseline (49 / 50 : ℝ)) (1797263411 / 1000000000000 : ℝ) (449315967 / 250000000000 : ℝ) := by
  exact b776

lemma baseline_enclosure_102 : Encl (twoChordBaseline (51 / 50 : ℝ)) (926954813 / 1000000000000 : ℝ) (926955277 / 1000000000000 : ℝ) := by
  exact b923

lemma gain_enclosure_102 : Encl (gain (51 / 50 : ℝ)) (385016519 / 500000000000 : ℝ) (9625413 / 12500000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b963

lemma baseline_enclosure_106 : Encl (twoChordBaseline (53 / 50 : ℝ)) (727511 / 3906250000 : ℝ) (23280411 / 125000000000 : ℝ) := by
  exact b1110

lemma gain_enclosure_106 : Encl (gain (53 / 50 : ℝ)) (495349959 / 500000000000 : ℝ) (495349961 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1144

lemma baseline_enclosure_110 : Encl (twoChordBaseline (11 / 10 : ℝ)) (-107195367 / 250000000000 : ℝ) (-107195259 / 250000000000 : ℝ) := by
  exact b1291

lemma gain_enclosure_110 : Encl (gain (11 / 10 : ℝ)) (1242385399 / 1000000000000 : ℝ) (621192701 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1325

lemma baseline_enclosure_114 : Encl (twoChordBaseline (57 / 50 : ℝ)) (-924869053 / 1000000000000 : ℝ) (-115608569 / 125000000000 : ℝ) := by
  exact b1472

lemma gain_enclosure_114 : Encl (gain (57 / 50 : ℝ)) (190443917 / 125000000000 : ℝ) (1523551339 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1506

lemma baseline_enclosure_118 : Encl (twoChordBaseline (59 / 50 : ℝ)) (-131180011 / 100000000000 : ℝ) (-1311799581 / 1000000000000 : ℝ) := by
  exact b1653

lemma gain_enclosure_118 : Encl (gain (59 / 50 : ℝ)) (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1687

lemma baseline_enclosure_122 : Encl (twoChordBaseline (61 / 50 : ℝ)) (-1602774927 / 1000000000000 : ℝ) (-400693599 / 250000000000 : ℝ) := by
  exact b1834

lemma gain_enclosure_122 : Encl (gain (61 / 50 : ℝ)) (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b1868

lemma baseline_enclosure_126 : Encl (twoChordBaseline (63 / 50 : ℝ)) (-72604479 / 40000000000 : ℝ) (-1815111389 / 1000000000000 : ℝ) := by
  exact b2015

lemma gain_enclosure_126 : Encl (gain (63 / 50 : ℝ)) (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2049

lemma baseline_enclosure_130 : Encl (twoChordBaseline (13 / 10 : ℝ)) (-985718467 / 500000000000 : ℝ) (-98571817 / 50000000000 : ℝ) := by
  exact b2196

lemma gain_enclosure_130 : Encl (gain (13 / 10 : ℝ)) (1363209939 / 500000000000 : ℝ) (1363209939 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2230

lemma baseline_enclosure_134 : Encl (twoChordBaseline (67 / 50 : ℝ)) (-84067367 / 40000000000 : ℝ) (-84067341 / 40000000000 : ℝ) := by
  exact b2377

lemma gain_enclosure_134 : Encl (gain (67 / 50 : ℝ)) (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2411

lemma baseline_enclosure_138 : Encl (twoChordBaseline (69 / 50 : ℝ)) (-35098821 / 15625000000 : ℝ) (-1123161939 / 500000000000 : ℝ) := by
  exact b2558

lemma gain_enclosure_138 : Encl (gain (69 / 50 : ℝ)) (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2592

lemma baseline_enclosure_142 : Encl (twoChordBaseline (71 / 50 : ℝ)) (-491832859 / 200000000000 : ℝ) (-1229581701 / 500000000000 : ℝ) := by
  exact b2739

lemma gain_enclosure_142 : Encl (gain (71 / 50 : ℝ)) (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2773

lemma baseline_enclosure_146 : Encl (linearBaseline (73 / 50 : ℝ)) (-2731694911 / 1000000000000 : ℝ) (-6829237 / 2500000000 : ℝ) := by
  exact b2822

lemma gain_enclosure_146 : Encl (gain (73 / 50 : ℝ)) (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2856

lemma baseline_enclosure_150 : Encl (linearBaseline (3 / 2 : ℝ)) (-2587585731 / 1000000000000 : ℝ) (-2587585621 / 1000000000000 : ℝ) := by
  exact b2905

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
