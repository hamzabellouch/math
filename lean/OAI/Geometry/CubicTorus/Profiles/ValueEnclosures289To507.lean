import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures72To288

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

def e289 : ℝ := e5 - e288
lemma b289 : Encl e289 (9382736463 / 12500000000 : ℝ) (187654729261 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b288 (by norm_num) (by norm_num)

def e290 : ℝ := e289 / e224
lemma b290 : Encl e290 (869334843491 / 1000000000000 : ℝ) (869334843499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b289 b224 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e291 : ℝ := e5 - e290
lemma b291 : Encl e291 (130665156501 / 1000000000000 : ℝ) (130665156509 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b290 (by norm_num) (by norm_num)

def e292 : ℝ := e287 - e291
lemma b292 : Encl e292 (93913016513 / 500000000000 : ℝ) (93913016523 / 500000000000 : ℝ) := by
  exact Encl.sub b287 b291 (by norm_num) (by norm_num)

def e293 : ℝ := e280 * e292
lemma b293 : Encl e293 (19850040641 / 1000000000000 : ℝ) (4962510163 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b280 b292 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e294 : ℝ := e278 - e268
lemma b294 : Encl e294 (59199521701 / 500000000000 : ℝ) (59199521731 / 500000000000 : ℝ) := by
  exact Encl.sub b278 b268 (by norm_num) (by norm_num)

def e295 : ℝ := e5 + e285
lemma b295 : Encl e295 (1664715029521 / 1000000000000 : ℝ) (66588601181 / 40000000000 : ℝ) := by
  exact Encl.add b5 b285 (by norm_num) (by norm_num)

def e296 : ℝ := e259 / e295
lemma b296 : Encl e296 (448783718633 / 1000000000000 : ℝ) (448783718637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b295 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e297 : ℝ := e296 ^ 2
lemma b297 : Encl e297 (20140682611 / 100000000000 : ℝ) (100703413057 / 500000000000 : ℝ) := by
  exact Encl.pow b296 (by norm_num) 2 (by norm_num) (by norm_num)

def e298 : ℝ := e5 + e297
lemma b298 : Encl e298 (120140682611 / 100000000000 : ℝ) (600703413057 / 500000000000 : ℝ) := by
  exact Encl.add b5 b297 (by norm_num) (by norm_num)

def e299 : ℝ := Real.sqrt e298
lemma b299 : Encl e299 (1096087052249 / 1000000000000 : ℝ) (274021763063 / 250000000000 : ℝ) := by
  exact Encl.sqrt b298 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e300 : ℝ := e5 + e299
lemma b300 : Encl e300 (2096087052249 / 1000000000000 : ℝ) (524021763063 / 250000000000 : ℝ) := by
  exact Encl.add b5 b299 (by norm_num) (by norm_num)

def e301 : ℝ := e296 / e300
lemma b301 : Encl e301 (214105477227 / 1000000000000 : ℝ) (21410547723 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b296 b300 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e302 : ℝ := Real.arcsin e259
lemma b302 : Encl e302 (421842005297 / 500000000000 : ℝ) (843684010607 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e259) (a := (214105477227 / 1000000000000 : ℝ)) (b := (21410547723 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (93387125177 / 125000000000 : ℝ) by norm_num).trans b259.1
        exact b259.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e259) (214105477227 / 1000000000000 : ℝ) (21410547723 / 100000000000 : ℝ) from b301) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e303 : ℝ := e59 * e302
lemma b303 : Encl e303 (215139422701 / 500000000000 : ℝ) (43027884541 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b302 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e304 : ℝ := e61 * e259
lemma b304 : Encl e304 (366077530693 / 1000000000000 : ℝ) (73215506139 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b259 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e305 : ℝ := e304 * e285
lemma b305 : Encl e305 (243337236621 / 1000000000000 : ℝ) (1946697893 / 8000000000 : ℝ) := by
  exact Encl.mul_nonneg b304 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e306 : ℝ := e303 - e305
lemma b306 : Encl e306 (186941608777 / 1000000000000 : ℝ) (186941608789 / 1000000000000 : ℝ) := by
  exact Encl.sub b303 b305 (by norm_num) (by norm_num)

def e307 : ℝ := e43 * e285
lemma b307 : Encl e307 (664715029521 / 20000000000 : ℝ) (26588601181 / 800000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b285 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e308 : ℝ := e259 / e307
lemma b308 : Encl e308 (11239357743 / 500000000000 : ℝ) (22478715487 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b259 b307 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e309 : ℝ := e306 - e308
lemma b309 : Encl e309 (16446289329 / 100000000000 : ℝ) (164462893303 / 1000000000000 : ℝ) := by
  exact Encl.sub b306 b308 (by norm_num) (by norm_num)

def e310 : ℝ := e309 - e239
lemma b310 : Encl e310 (11991322149 / 100000000000 : ℝ) (119913221513 / 1000000000000 : ℝ) := by
  exact Encl.sub b309 b239 (by norm_num) (by norm_num)

def e311 : ℝ := e294 * e310
lemma b311 : Encl e311 (2839522143 / 200000000000 : ℝ) (7098805363 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b294 b310 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e312 : ℝ := e293 + e311
lemma b312 : Encl e312 (8511912839 / 250000000000 : ℝ) (17023825689 / 500000000000 : ℝ) := by
  exact Encl.add b293 b311 (by norm_num) (by norm_num)

def e313 : ℝ := e259 - e192
lemma b313 : Encl e313 (242646317191 / 1000000000000 : ℝ) (48529263439 / 200000000000 : ℝ) := by
  exact Encl.sub b259 b192 (by norm_num) (by norm_num)

def e314 : ℝ := e312 / e313
lemma b314 : Encl e314 (2192469099 / 15625000000 : ℝ) (14031802243 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b312 b313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e315 : ℝ := e257 + e314
lemma b315 : Encl e315 (-163442449187 / 500000000000 : ℝ) (-10215153069 / 31250000000 : ℝ) := by
  exact Encl.add b257 b314 (by norm_num) (by norm_num)

def e316 : ℝ := e4 * e278
lemma b316 : Encl e316 (791882897663 / 1000000000000 : ℝ) (791882897697 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e317 : ℝ := e4 / e190
lemma b317 : Encl e317 (668745485547 / 500000000000 : ℝ) (167186371387 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b190 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e318 : ℝ := e89 * e317
lemma b318 : Encl e318 (1185320511133 / 500000000000 : ℝ) (37041265973 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b317 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e319 : ℝ := e317 ^ 2
lemma b319 : Encl e319 (1788882097757 / 1000000000000 : ℝ) (447220524441 / 250000000000 : ℝ) := by
  exact Encl.pow b317 (by norm_num) 2 (by norm_num) (by norm_num)

def e320 : ℝ := e91 * e319
lemma b320 : Encl e320 (10976443079 / 7812500000 : ℝ) (35124617853 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e321 : ℝ := e5 + e320
lemma b321 : Encl e321 (18788943079 / 7812500000 : ℝ) (60124617853 / 25000000000 : ℝ) := by
  exact Encl.add b5 b320 (by norm_num) (by norm_num)

def e322 : ℝ := Real.sqrt e321
lemma b322 : Encl e322 (1550801313551 / 1000000000000 : ℝ) (775400656777 / 500000000000 : ℝ) := by
  exact Encl.sqrt b321 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e323 : ℝ := e318 * e322
lemma b323 : Encl e323 (3676393211287 / 1000000000000 : ℝ) (735278642261 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b318 b322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e324 : ℝ := e97 * e319
lemma b324 : Encl e324 (10976443079 / 3906250000 : ℝ) (1404984714119 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e325 : ℝ := e323 - e324
lemma b325 : Encl e325 (866423783049 / 1000000000000 : ℝ) (866423783081 / 1000000000000 : ℝ) := by
  exact Encl.sub b323 b324 (by norm_num) (by norm_num)

def e326 : ℝ := e259 * e325
lemma b326 : Encl e326 (647302610271 / 1000000000000 : ℝ) (323651305149 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b259 b325 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e327 : ℝ := e316 - e326
lemma b327 : Encl e327 (28916057473 / 200000000000 : ℝ) (72290143713 / 500000000000 : ℝ) := by
  exact Encl.sub b316 b326 (by norm_num) (by norm_num)

def e328 : ℝ := e165 - e287
lemma b328 : Encl e328 (100377202607 / 250000000000 : ℝ) (401508810493 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b287 (by norm_num) (by norm_num)

def e329 : ℝ := e327 * e328
lemma b329 : Encl e329 (58050259191 / 1000000000000 : ℝ) (29025129613 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b327 b328 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e330 : ℝ := e325 - e278
lemma b330 : Encl e330 (8291828223 / 125000000000 : ℝ) (8291828231 / 125000000000 : ℝ) := by
  exact Encl.sub b325 b278 (by norm_num) (by norm_num)

def e331 : ℝ := e183 - e309
lemma b331 : Encl e331 (355689876209 / 1000000000000 : ℝ) (355689876353 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b309 (by norm_num) (by norm_num)

def e332 : ℝ := e330 * e331
lemma b332 : Encl e332 (23594554833 / 1000000000000 : ℝ) (11797277433 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b330 b331 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e333 : ℝ := e329 + e332
lemma b333 : Encl e333 (10205601753 / 125000000000 : ℝ) (20411203523 / 250000000000 : ℝ) := by
  exact Encl.add b329 b332 (by norm_num) (by norm_num)

def e334 : ℝ := e4 - e259
lemma b334 : Encl e334 (30330789649 / 125000000000 : ℝ) (48529263439 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b259 (by norm_num) (by norm_num)

def e335 : ℝ := e333 / e334
lemma b335 : Encl e335 (336476625599 / 1000000000000 : ℝ) (67295325177 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b333 b334 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e336 : ℝ := e315 + e335
lemma b336 : Encl e336 (383669089 / 40000000000 : ℝ) (9591727677 / 1000000000000 : ℝ) := by
  exact Encl.add b315 b335 (by norm_num) (by norm_num)

def e337 : ℝ := (21 / 25 : ℝ)
lemma b337 : Encl e337 (21 / 25 : ℝ) (21 / 25 : ℝ) := by
  exact Encl.exact (21 / 25 : ℝ)

def e338 : ℝ := e337 / e0
lemma b338 : Encl e338 (133690152197 / 500000000000 : ℝ) (53476060879 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b337 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e339 : ℝ := e337 * e7
lemma b339 : Encl e339 (114523939121 / 200000000000 : ℝ) (572619695607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b337 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e340 : ℝ := e8 * e337
lemma b340 : Encl e340 (1029 / 1250 : ℝ) (1029 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b8 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e341 : ℝ := e340 / e0
lemma b341 : Encl e341 (131016349153 / 500000000000 : ℝ) (262032698307 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b340 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e342 : ℝ := e337 ^ 2
lemma b342 : Encl e342 (441 / 625 : ℝ) (441 / 625 : ℝ) := by
  exact Encl.pow b337 (by norm_num) 2 (by norm_num) (by norm_num)

def e343 : ℝ := e17 * e342
lemma b343 : Encl e343 (1764 / 625 : ℝ) (1764 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b342 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e344 : ℝ := e343 / e0
lemma b344 : Encl e344 (179679564553 / 200000000000 : ℝ) (449198911383 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b343 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e345 : ℝ := e5 + e344
lemma b345 : Encl e345 (379679564553 / 200000000000 : ℝ) (949198911383 / 500000000000 : ℝ) := by
  exact Encl.add b5 b344 (by norm_num) (by norm_num)

def e346 : ℝ := Real.sqrt e345
lemma b346 : Encl e346 (86113973867 / 62500000000 : ℝ) (688911790937 / 500000000000 : ℝ) := by
  exact Encl.sqrt b345 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e347 : ℝ := e5 + e346
lemma b347 : Encl e347 (148613973867 / 62500000000 : ℝ) (1188911790937 / 500000000000 : ℝ) := by
  exact Encl.add b5 b346 (by norm_num) (by norm_num)

def e348 : ℝ := e23 / e347
lemma b348 : Encl e348 (33644211711 / 40000000000 : ℝ) (105138161597 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b347 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e349 : ℝ := e9 * e348
lemma b349 : Encl e349 (235509481977 / 1000000000000 : ℝ) (117754740989 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e350 : ℝ := e341 + e349
lemma b350 : Encl e350 (497542180283 / 1000000000000 : ℝ) (99508436057 / 200000000000 : ℝ) := by
  exact Encl.add b341 b349 (by norm_num) (by norm_num)

def e351 : ℝ := e350 - e5
lemma b351 : Encl e351 (-502457819717 / 1000000000000 : ℝ) (-100491563943 / 200000000000 : ℝ) := by
  exact Encl.sub b350 b5 (by norm_num) (by norm_num)

def e352 : ℝ := e0 / e342
lemma b352 : Encl e352 (4452370540801 / 1000000000000 : ℝ) (2226185270401 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b342 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e353 : ℝ := e338 ^ 2
lemma b353 : Encl e353 (71492227177 / 1000000000000 : ℝ) (71492227179 / 1000000000000 : ℝ) := by
  exact Encl.pow b338 (by norm_num) 2 (by norm_num) (by norm_num)

def e354 : ℝ := e5 - e353
lemma b354 : Encl e354 (928507772821 / 1000000000000 : ℝ) (928507772823 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b353 (by norm_num) (by norm_num)

def e355 : ℝ := Real.sqrt e354
lemma b355 : Encl e355 (481795540873 / 500000000000 : ℝ) (240897770437 / 250000000000 : ℝ) := by
  exact Encl.sqrt b354 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e356 : ℝ := e29 - e355
lemma b356 : Encl e356 (-148462207541 / 500000000000 : ℝ) (-296924415079 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b355 (by norm_num) (by norm_num)

def e357 : ℝ := e355 ^ 3
lemma b357 : Encl e357 (894701809221 / 1000000000000 : ℝ) (223675452307 / 250000000000 : ℝ) := by
  exact Encl.pow b355 (by norm_num) 3 (by norm_num) (by norm_num)

def e358 : ℝ := e357 / e35
lemma b358 : Encl e358 (298233936407 / 1000000000000 : ℝ) (29823393641 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b357 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e359 : ℝ := e356 + e358
lemma b359 : Encl e359 (52380853 / 40000000000 : ℝ) (1309521331 / 1000000000000 : ℝ) := by
  exact Encl.add b356 b358 (by norm_num) (by norm_num)

def e360 : ℝ := e8 * e359
lemma b360 : Encl e360 (641665449 / 500000000000 : ℝ) (256666181 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b359 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e361 : ℝ := e353 / e355
lemma b361 : Encl e361 (2318547921 / 31250000000 : ℝ) (2967741339 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b353 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e362 : ℝ := e361 - e23
lemma b362 : Encl e362 (-60181452079 / 31250000000 : ℝ) (-77032258661 / 40000000000 : ℝ) := by
  exact Encl.sub b361 b23 (by norm_num) (by norm_num)

def e363 : ℝ := e23 * e355
lemma b363 : Encl e363 (481795540873 / 250000000000 : ℝ) (240897770437 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e364 : ℝ := e362 + e363
lemma b364 : Encl e364 (343924241 / 250000000000 : ℝ) (1375696971 / 1000000000000 : ℝ) := by
  exact Encl.add b362 b363 (by norm_num) (by norm_num)

def e365 : ℝ := e364 / e43
lemma b365 : Encl e365 (27513939 / 1000000000000 : ℝ) (1375697 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b364 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e366 : ℝ := e360 - e365
lemma b366 : Encl e366 (627908479 / 500000000000 : ℝ) (627908483 / 500000000000 : ℝ) := by
  exact Encl.sub b360 b365 (by norm_num) (by norm_num)

def e367 : ℝ := e352 * e366
lemma b367 : Encl e367 (1397840607 / 250000000000 : ℝ) (1118272493 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b352 b366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e368 : ℝ := e351 + e367
lemma b368 : Encl e368 (-496866457289 / 1000000000000 : ℝ) (-1987465829 / 4000000000 : ℝ) := by
  exact Encl.add b351 b367 (by norm_num) (by norm_num)

def e369 : ℝ := e339 ^ 2
lemma b369 : Encl e369 (163946657897 / 500000000000 : ℝ) (163946657899 / 500000000000 : ℝ) := by
  exact Encl.pow b339 (by norm_num) 2 (by norm_num) (by norm_num)

def e370 : ℝ := e5 - e369
lemma b370 : Encl e370 (336053342101 / 500000000000 : ℝ) (336053342103 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b369 (by norm_num) (by norm_num)

def e371 : ℝ := Real.sqrt e370
lemma b371 : Encl e371 (409910564697 / 500000000000 : ℝ) (409910564699 / 500000000000 : ℝ) := by
  exact Encl.sqrt b370 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e372 : ℝ := e5 + e371
lemma b372 : Encl e372 (909910564697 / 500000000000 : ℝ) (909910564699 / 500000000000 : ℝ) := by
  exact Encl.add b5 b371 (by norm_num) (by norm_num)

def e373 : ℝ := e339 / e372
lemma b373 : Encl e373 (78664282763 / 250000000000 : ℝ) (62931426211 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b372 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e374 : ℝ := e373 ^ 2
lemma b374 : Encl e374 (99009110121 / 1000000000000 : ℝ) (24752277531 / 250000000000 : ℝ) := by
  exact Encl.pow b373 (by norm_num) 2 (by norm_num) (by norm_num)

def e375 : ℝ := e5 + e374
lemma b375 : Encl e375 (1099009110121 / 1000000000000 : ℝ) (274752277531 / 250000000000 : ℝ) := by
  exact Encl.add b5 b374 (by norm_num) (by norm_num)

def e376 : ℝ := Real.sqrt e375
lemma b376 : Encl e376 (262084088381 / 250000000000 : ℝ) (524168176763 / 500000000000 : ℝ) := by
  exact Encl.sqrt b375 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e377 : ℝ := e5 + e376
lemma b377 : Encl e377 (512084088381 / 250000000000 : ℝ) (1024168176763 / 500000000000 : ℝ) := by
  exact Encl.add b5 b376 (by norm_num) (by norm_num)

def e378 : ℝ := e373 / e377
lemma b378 : Encl e378 (153615948137 / 1000000000000 : ℝ) (7680797407 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b373 b377 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e379 : ℝ := Real.arcsin e339
lemma b379 : Encl e379 (304848875169 / 500000000000 : ℝ) (609697750351 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e339) (a := (153615948137 / 1000000000000 : ℝ)) (b := (7680797407 / 50000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (114523939121 / 200000000000 : ℝ) by norm_num).trans b339.1
        exact b339.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e339) (153615948137 / 1000000000000 : ℝ) (7680797407 / 50000000000 : ℝ) from b378) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e380 : ℝ := e59 * e379
lemma b380 : Encl e380 (1214632237 / 3906250000 : ℝ) (7773646317 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b379 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e381 : ℝ := e61 * e339
lemma b381 : Encl e381 (140291825423 / 500000000000 : ℝ) (8768239089 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b339 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e382 : ℝ := e381 * e371
lemma b382 : Encl e382 (115014202763 / 500000000000 : ℝ) (230028405529 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b381 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e383 : ℝ := e380 - e382
lemma b383 : Encl e383 (80917447143 / 1000000000000 : ℝ) (40458723577 / 500000000000 : ℝ) := by
  exact Encl.sub b380 b382 (by norm_num) (by norm_num)

def e384 : ℝ := e43 * e371
lemma b384 : Encl e384 (409910564697 / 10000000000 : ℝ) (409910564699 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e385 : ℝ := e339 / e384
lemma b385 : Encl e385 (109135791 / 7812500000 : ℝ) (13969381249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e386 : ℝ := e383 - e385
lemma b386 : Encl e386 (33474032947 / 500000000000 : ℝ) (33474032953 / 500000000000 : ℝ) := by
  exact Encl.sub b383 b385 (by norm_num) (by norm_num)

def e387 : ℝ := e5 + e355
lemma b387 : Encl e387 (981795540873 / 500000000000 : ℝ) (490897770437 / 250000000000 : ℝ) := by
  exact Encl.add b5 b355 (by norm_num) (by norm_num)

def e388 : ℝ := e338 / e387
lemma b388 : Encl e388 (34042258961 / 250000000000 : ℝ) (27233807169 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b338 b387 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e389 : ℝ := e388 ^ 2
lemma b389 : Encl e389 (9271003161 / 500000000000 : ℝ) (18542006323 / 1000000000000 : ℝ) := by
  exact Encl.pow b388 (by norm_num) 2 (by norm_num) (by norm_num)

def e390 : ℝ := e5 + e389
lemma b390 : Encl e390 (509271003161 / 500000000000 : ℝ) (1018542006323 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b389 (by norm_num) (by norm_num)

def e391 : ℝ := Real.sqrt e390
lemma b391 : Encl e391 (1009228421281 / 1000000000000 : ℝ) (504614210641 / 500000000000 : ℝ) := by
  exact Encl.sqrt b390 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e392 : ℝ := e5 + e391
lemma b392 : Encl e392 (2009228421281 / 1000000000000 : ℝ) (1004614210641 / 500000000000 : ℝ) := by
  exact Encl.add b5 b391 (by norm_num) (by norm_num)

def e393 : ℝ := e388 / e392
lemma b393 : Encl e393 (3388590227 / 50000000000 : ℝ) (67771804541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b388 b392 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e394 : ℝ := Real.arcsin e338
lemma b394 : Encl e394 (27067332207 / 100000000000 : ℝ) (10826932883 / 40000000000 : ℝ) := by
  apply Encl.arcsin (z := e338) (a := (3388590227 / 50000000000 : ℝ)) (b := (67771804541 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (133690152197 / 500000000000 : ℝ) by norm_num).trans b338.1
        exact b338.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e338) (3388590227 / 50000000000 : ℝ) (67771804541 / 1000000000000 : ℝ) from b393) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e395 : ℝ := e59 * e394
lemma b395 : Encl e395 (27608678851 / 200000000000 : ℝ) (138043394259 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b394 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e396 : ℝ := e61 * e338
lemma b396 : Encl e396 (131016349153 / 1000000000000 : ℝ) (65508174577 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b338 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e397 : ℝ := e396 * e355
lemma b397 : Encl e397 (63123092803 / 500000000000 : ℝ) (15780773201 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b396 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e398 : ℝ := e395 - e397
lemma b398 : Encl e398 (11797208647 / 1000000000000 : ℝ) (11797208653 / 1000000000000 : ℝ) := by
  exact Encl.sub b395 b397 (by norm_num) (by norm_num)

def e399 : ℝ := e43 * e355
lemma b399 : Encl e399 (481795540873 / 10000000000 : ℝ) (240897770437 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b355 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e400 : ℝ := e338 / e399
lemma b400 : Encl e400 (2774831663 / 500000000000 : ℝ) (5549663327 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b338 b399 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e401 : ℝ := e398 - e400
lemma b401 : Encl e401 (156188633 / 25000000000 : ℝ) (6247545327 / 1000000000000 : ℝ) := by
  exact Encl.sub b398 b400 (by norm_num) (by norm_num)

def e402 : ℝ := e386 - e401
lemma b402 : Encl e402 (60700520567 / 1000000000000 : ℝ) (30350260293 / 500000000000 : ℝ) := by
  exact Encl.sub b386 b401 (by norm_num) (by norm_num)

def e403 : ℝ := e402 / e337
lemma b403 : Encl e403 (18065631121 / 250000000000 : ℝ) (18065631127 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b402 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e404 : ℝ := e368 + e403
lemma b404 : Encl e404 (-84920786561 / 200000000000 : ℝ) (-212301966371 / 500000000000 : ℝ) := by
  exact Encl.add b368 b403 (by norm_num) (by norm_num)

def e405 : ℝ := e339 + e4
lemma b405 : Encl e405 (312472602843 / 200000000000 : ℝ) (781181507109 / 500000000000 : ℝ) := by
  exact Encl.add b339 b4 (by norm_num) (by norm_num)

def e406 : ℝ := e405 / e23
lemma b406 : Encl e406 (781181507107 / 1000000000000 : ℝ) (781181507109 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b405 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e407 : ℝ := e339 / e337
lemma b407 : Encl e407 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b339 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e408 : ℝ := e89 * e407
lemma b408 : Encl e408 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b407 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e409 : ℝ := e407 ^ 2
lemma b409 : Encl e409 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b407 (by norm_num) 2 (by norm_num) (by norm_num)

def e410 : ℝ := e91 * e409
lemma b410 : Encl e410 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b409 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e411 : ℝ := e5 + e410
lemma b411 : Encl e411 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b410 (by norm_num) (by norm_num)

def e412 : ℝ := Real.sqrt e411
lemma b412 : Encl e412 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b411 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e413 : ℝ := e408 * e412
lemma b413 : Encl e413 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b408 b412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e414 : ℝ := e97 * e409
lemma b414 : Encl e414 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b409 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e415 : ℝ := e413 - e414
lemma b415 : Encl e415 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b413 b414 (by norm_num) (by norm_num)

def e416 : ℝ := e406 * e415
lemma b416 : Encl e416 (266261855241 / 500000000000 : ℝ) (266261855251 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b406 b415 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e417 : ℝ := e406 / e337
lemma b417 : Encl e417 (929977984651 / 1000000000000 : ℝ) (464988992327 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e418 : ℝ := e89 * e417
lemma b418 : Encl e418 (1648343060151 / 1000000000000 : ℝ) (824171530079 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e419 : ℝ := e417 ^ 2
lemma b419 : Encl e419 (172971810387 / 200000000000 : ℝ) (432429525971 / 500000000000 : ℝ) := by
  exact Encl.pow b417 (by norm_num) 2 (by norm_num) (by norm_num)

def e420 : ℝ := e91 * e419
lemma b420 : Encl e420 (679258710987 / 1000000000000 : ℝ) (339629355497 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b419 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e421 : ℝ := e5 + e420
lemma b421 : Encl e421 (1679258710987 / 1000000000000 : ℝ) (839629355497 / 500000000000 : ℝ) := by
  exact Encl.add b5 b420 (by norm_num) (by norm_num)

def e422 : ℝ := Real.sqrt e421
lemma b422 : Encl e422 (259172429937 / 200000000000 : ℝ) (161982768711 / 125000000000 : ℝ) := by
  exact Encl.sqrt b421 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e423 : ℝ := e418 * e422
lemma b423 : Encl e423 (427205076269 / 200000000000 : ℝ) (26700317267 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b418 b422 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e424 : ℝ := e97 * e419
lemma b424 : Encl e424 (679258710987 / 500000000000 : ℝ) (679258710993 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b419 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e425 : ℝ := e423 - e424
lemma b425 : Encl e425 (777507959359 / 1000000000000 : ℝ) (388753979693 / 500000000000 : ℝ) := by
  exact Encl.sub b423 b424 (by norm_num) (by norm_num)

def e426 : ℝ := e339 * e425
lemma b426 : Encl e426 (222608185509 / 500000000000 : ℝ) (111304092759 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b339 b425 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e427 : ℝ := e416 - e426
lemma b427 : Encl e427 (43653669723 / 500000000000 : ℝ) (21826834871 / 250000000000 : ℝ) := by
  exact Encl.sub b416 b426 (by norm_num) (by norm_num)

def e428 : ℝ := e406 ^ 2
lemma b428 : Encl e428 (122048909409 / 200000000000 : ℝ) (12204890941 / 20000000000 : ℝ) := by
  exact Encl.pow b406 (by norm_num) 2 (by norm_num) (by norm_num)

def e429 : ℝ := e8 * e428
lemma b429 : Encl e429 (74754957013 / 125000000000 : ℝ) (598039656109 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b428 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e430 : ℝ := e5 - e429
lemma b430 : Encl e430 (401960343891 / 1000000000000 : ℝ) (50245042987 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b429 (by norm_num) (by norm_num)

def e431 : ℝ := e5 - e428
lemma b431 : Encl e431 (7795109059 / 20000000000 : ℝ) (77951090591 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b428 (by norm_num) (by norm_num)

def e432 : ℝ := Real.sqrt e431
lemma b432 : Encl e432 (624303974799 / 1000000000000 : ℝ) (156075993701 / 250000000000 : ℝ) := by
  exact Encl.sqrt b431 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e433 : ℝ := e430 / e432
lemma b433 : Encl e433 (321926785759 / 500000000000 : ℝ) (643853571533 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b430 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e434 : ℝ := e5 - e433
lemma b434 : Encl e434 (356146428467 / 1000000000000 : ℝ) (178073214241 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b433 (by norm_num) (by norm_num)

def e435 : ℝ := e8 * e369
lemma b435 : Encl e435 (160667724739 / 500000000000 : ℝ) (321335449483 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b369 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e436 : ℝ := e5 - e435
lemma b436 : Encl e436 (678664550517 / 1000000000000 : ℝ) (339332275261 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b435 (by norm_num) (by norm_num)

def e437 : ℝ := e436 / e371
lemma b437 : Encl e437 (206955068057 / 250000000000 : ℝ) (827820272239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b436 b371 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e438 : ℝ := e5 - e437
lemma b438 : Encl e438 (172179727761 / 1000000000000 : ℝ) (43044931943 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b437 (by norm_num) (by norm_num)

def e439 : ℝ := e434 - e438
lemma b439 : Encl e439 (36793340139 / 200000000000 : ℝ) (183966700721 / 1000000000000 : ℝ) := by
  exact Encl.sub b434 b438 (by norm_num) (by norm_num)

def e440 : ℝ := e427 * e439
lemma b440 : Encl e440 (1003852699 / 62500000000 : ℝ) (8030821597 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b427 b439 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e441 : ℝ := e425 - e415
lemma b441 : Encl e441 (95817845531 / 1000000000000 : ℝ) (95817845581 / 1000000000000 : ℝ) := by
  exact Encl.sub b425 b415 (by norm_num) (by norm_num)

def e442 : ℝ := e5 + e432
lemma b442 : Encl e442 (1624303974799 / 1000000000000 : ℝ) (406075993701 / 250000000000 : ℝ) := by
  exact Encl.add b5 b432 (by norm_num) (by norm_num)

def e443 : ℝ := e406 / e442
lemma b443 : Encl e443 (480933076089 / 1000000000000 : ℝ) (480933076093 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b442 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e444 : ℝ := e443 ^ 2
lemma b444 : Encl e444 (57824155919 / 250000000000 : ℝ) (231296623681 / 1000000000000 : ℝ) := by
  exact Encl.pow b443 (by norm_num) 2 (by norm_num) (by norm_num)

def e445 : ℝ := e5 + e444
lemma b445 : Encl e445 (307824155919 / 250000000000 : ℝ) (1231296623681 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b444 (by norm_num) (by norm_num)

def e446 : ℝ := Real.sqrt e445
lemma b446 : Encl e446 (1109638059763 / 1000000000000 : ℝ) (554819029883 / 500000000000 : ℝ) := by
  exact Encl.sqrt b445 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e447 : ℝ := e5 + e446
lemma b447 : Encl e447 (2109638059763 / 1000000000000 : ℝ) (1054819029883 / 500000000000 : ℝ) := by
  exact Encl.add b5 b446 (by norm_num) (by norm_num)

def e448 : ℝ := e443 / e447
lemma b448 : Encl e448 (227969472707 / 1000000000000 : ℝ) (22796947271 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b443 b447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e449 : ℝ := Real.arcsin e406
lemma b449 : Encl e449 (896556101783 / 1000000000000 : ℝ) (179311220359 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e406) (a := (227969472707 / 1000000000000 : ℝ)) (b := (22796947271 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (781181507107 / 1000000000000 : ℝ) by norm_num).trans b406.1
        exact b406.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e406) (227969472707 / 1000000000000 : ℝ) (22796947271 / 100000000000 : ℝ) from b448) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e450 : ℝ := e59 * e449
lemma b450 : Encl e450 (457243611909 / 1000000000000 : ℝ) (114310902979 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b449 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e451 : ℝ := e61 * e406
lemma b451 : Encl e451 (191389469241 / 500000000000 : ℝ) (95694734621 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e452 : ℝ := e451 * e432
lemma b452 : Encl e452 (238970412763 / 1000000000000 : ℝ) (238970412767 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b451 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e453 : ℝ := e450 - e452
lemma b453 : Encl e453 (109136599571 / 500000000000 : ℝ) (218273199153 / 1000000000000 : ℝ) := by
  exact Encl.sub b450 b452 (by norm_num) (by norm_num)

def e454 : ℝ := e43 * e432
lemma b454 : Encl e454 (624303974799 / 20000000000 : ℝ) (156075993701 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b432 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e455 : ℝ := e406 / e454
lemma b455 : Encl e455 (25025677831 / 1000000000000 : ℝ) (3128209729 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b406 b454 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e456 : ℝ := e453 - e455
lemma b456 : Encl e456 (19324752131 / 100000000000 : ℝ) (96623760661 / 500000000000 : ℝ) := by
  exact Encl.sub b453 b455 (by norm_num) (by norm_num)

def e457 : ℝ := e456 - e386
lemma b457 : Encl e457 (31574863851 / 250000000000 : ℝ) (31574863857 / 250000000000 : ℝ) := by
  exact Encl.sub b456 b386 (by norm_num) (by norm_num)

def e458 : ℝ := e441 * e457
lemma b458 : Encl e458 (3025435427 / 250000000000 : ℝ) (6050870859 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b441 b457 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e459 : ℝ := e440 + e458
lemma b459 : Encl e459 (7040846223 / 250000000000 : ℝ) (1760211557 / 62500000000 : ℝ) := by
  exact Encl.add b440 b458 (by norm_num) (by norm_num)

def e460 : ℝ := e406 - e339
lemma b460 : Encl e460 (417123623 / 2000000000 : ℝ) (13035113219 / 62500000000 : ℝ) := by
  exact Encl.sub b406 b339 (by norm_num) (by norm_num)

def e461 : ℝ := e459 / e460
lemma b461 : Encl e461 (135036153977 / 1000000000000 : ℝ) (33759038519 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b459 b460 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e462 : ℝ := e404 + e461
lemma b462 : Encl e462 (-72391944707 / 250000000000 : ℝ) (-144783889333 / 500000000000 : ℝ) := by
  exact Encl.add b404 b461 (by norm_num) (by norm_num)

def e463 : ℝ := e4 * e425
lemma b463 : Encl e463 (769533307941 / 1000000000000 : ℝ) (76953330797 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b425 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e464 : ℝ := e4 / e337
lemma b464 : Encl e464 (2301300499 / 1953125000 : ℝ) (117826585549 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b337 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e465 : ℝ := e89 * e464
lemma b465 : Encl e465 (2088421852949 / 1000000000000 : ℝ) (417684370591 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b464 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e466 : ℝ := e464 ^ 2
lemma b466 : Encl e466 (43384700819 / 31250000000 : ℝ) (694155213107 / 500000000000 : ℝ) := by
  exact Encl.pow b464 (by norm_num) 2 (by norm_num) (by norm_num)

def e467 : ℝ := e91 * e466
lemma b467 : Encl e467 (136297057371 / 125000000000 : ℝ) (43615058359 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b466 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e468 : ℝ := e5 + e467
lemma b468 : Encl e468 (261297057371 / 125000000000 : ℝ) (83615058359 / 40000000000 : ℝ) := by
  exact Encl.add b5 b467 (by norm_num) (by norm_num)

def e469 : ℝ := Real.sqrt e468
lemma b469 : Encl e469 (722906712337 / 500000000000 : ℝ) (1445813424677 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b468 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e470 : ℝ := e465 * e469
lemma b470 : Encl e470 (188716771961 / 62500000000 : ℝ) (94358385981 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b465 b469 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e471 : ℝ := e97 * e466
lemma b471 : Encl e471 (2180752917937 / 1000000000000 : ℝ) (2180752917949 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b466 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e472 : ℝ := e470 - e471
lemma b472 : Encl e472 (838715433427 / 1000000000000 : ℝ) (167743086691 / 200000000000 : ℝ) := by
  exact Encl.sub b470 b471 (by norm_num) (by norm_num)

def e473 : ℝ := e406 * e472
lemma b473 : Encl e473 (327594493159 / 500000000000 : ℝ) (327594493171 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b406 b472 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e474 : ℝ := e463 - e473
lemma b474 : Encl e474 (114344321599 / 1000000000000 : ℝ) (28586080413 / 250000000000 : ℝ) := by
  exact Encl.sub b463 b473 (by norm_num) (by norm_num)

def e475 : ℝ := e165 - e434
lemma b475 : Encl e475 (363853571493 / 1000000000000 : ℝ) (363853571561 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b434 (by norm_num) (by norm_num)

def e476 : ℝ := e474 * e475
lemma b476 : Encl e476 (41604589793 / 1000000000000 : ℝ) (41604589821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b474 b475 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e477 : ℝ := e472 - e425
lemma b477 : Encl e477 (61207474041 / 1000000000000 : ℝ) (3825467131 / 62500000000 : ℝ) := by
  exact Encl.sub b472 b425 (by norm_num) (by norm_num)

def e478 : ℝ := e183 - e456
lemma b478 : Encl e478 (32690524819 / 100000000000 : ℝ) (326905248333 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b456 (by norm_num) (by norm_num)

def e479 : ℝ := e477 * e478
lemma b479 : Encl e479 (5002261123 / 250000000000 : ℝ) (500226113 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b477 b478 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e480 : ℝ := e476 + e479
lemma b480 : Encl e480 (12322726857 / 200000000000 : ℝ) (61613634341 / 1000000000000 : ℝ) := by
  exact Encl.add b476 b479 (by norm_num) (by norm_num)

def e481 : ℝ := e4 - e406
lemma b481 : Encl e481 (208561811501 / 1000000000000 : ℝ) (13035113219 / 62500000000 : ℝ) := by
  exact Encl.sub b4 b406 (by norm_num) (by norm_num)

def e482 : ℝ := e480 / e481
lemma b482 : Encl e482 (73855364317 / 250000000000 : ℝ) (295421457541 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b480 b481 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e483 : ℝ := e462 + e482
lemma b483 : Encl e483 (146341961 / 25000000000 : ℝ) (46829431 / 8000000000 : ℝ) := by
  exact Encl.add b462 b482 (by norm_num) (by norm_num)

def e484 : ℝ := (23 / 25 : ℝ)
lemma b484 : Encl e484 (23 / 25 : ℝ) (23 / 25 : ℝ) := by
  exact Encl.exact (23 / 25 : ℝ)

def e485 : ℝ := e484 / e0
lemma b485 : Encl e485 (292845095289 / 1000000000000 : ℝ) (29284509529 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b484 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e486 : ℝ := e484 * e7
lemma b486 : Encl e486 (62715490471 / 100000000000 : ℝ) (78394363089 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b484 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e487 : ℝ := e8 * e484
lemma b487 : Encl e487 (1127 / 1250 : ℝ) (1127 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b8 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e488 : ℝ := e487 / e0
lemma b488 : Encl e488 (286988193383 / 1000000000000 : ℝ) (35873524173 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b487 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e489 : ℝ := e484 ^ 2
lemma b489 : Encl e489 (529 / 625 : ℝ) (529 / 625 : ℝ) := by
  exact Encl.pow b484 (by norm_num) 2 (by norm_num) (by norm_num)

def e490 : ℝ := e17 * e489
lemma b490 : Encl e490 (2116 / 625 : ℝ) (2116 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b489 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e491 : ℝ := e490 / e0
lemma b491 : Encl e491 (1077669950663 / 1000000000000 : ℝ) (134708743833 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b490 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e492 : ℝ := e5 + e491
lemma b492 : Encl e492 (2077669950663 / 1000000000000 : ℝ) (259708743833 / 125000000000 : ℝ) := by
  exact Encl.add b5 b491 (by norm_num) (by norm_num)

def e493 : ℝ := Real.sqrt e492
lemma b493 : Encl e493 (720706242283 / 500000000000 : ℝ) (1441412484567 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b492 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e494 : ℝ := e5 + e493
lemma b494 : Encl e494 (1220706242283 / 500000000000 : ℝ) (2441412484567 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b493 (by norm_num) (by norm_num)

def e495 : ℝ := e23 / e494
lemma b495 : Encl e495 (819197908031 / 1000000000000 : ℝ) (819197908033 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e496 : ℝ := e9 * e495
lemma b496 : Encl e496 (28671926781 / 125000000000 : ℝ) (917501657 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b495 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e497 : ℝ := e488 + e496
lemma b497 : Encl e497 (516363607631 / 1000000000000 : ℝ) (258181803817 / 500000000000 : ℝ) := by
  exact Encl.add b488 b496 (by norm_num) (by norm_num)

def e498 : ℝ := e497 - e5
lemma b498 : Encl e498 (-483636392369 / 1000000000000 : ℝ) (-241818196183 / 500000000000 : ℝ) := by
  exact Encl.sub b497 b5 (by norm_num) (by norm_num)

def e499 : ℝ := e0 / e489
lemma b499 : Encl e499 (1855855773623 / 500000000000 : ℝ) (3711711547247 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b489 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e500 : ℝ := e485 ^ 2
lemma b500 : Encl e500 (42879124917 / 500000000000 : ℝ) (21439562459 / 250000000000 : ℝ) := by
  exact Encl.pow b485 (by norm_num) 2 (by norm_num) (by norm_num)

def e501 : ℝ := e5 - e500
lemma b501 : Encl e501 (228560437541 / 250000000000 : ℝ) (457120875083 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b500 (by norm_num) (by norm_num)

def e502 : ℝ := Real.sqrt e501
lemma b502 : Encl e502 (956159897801 / 1000000000000 : ℝ) (956159897803 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b501 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e503 : ℝ := e29 - e502
lemma b503 : Encl e503 (-289493231137 / 1000000000000 : ℝ) (-144746615567 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b502 (by norm_num) (by norm_num)

def e504 : ℝ := e502 ^ 3
lemma b504 : Encl e504 (874161298401 / 1000000000000 : ℝ) (874161298407 / 1000000000000 : ℝ) := by
  exact Encl.pow b502 (by norm_num) 3 (by norm_num) (by norm_num)

def e505 : ℝ := e504 / e35
lemma b505 : Encl e505 (291387099467 / 1000000000000 : ℝ) (291387099469 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b504 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e506 : ℝ := e503 + e505
lemma b506 : Encl e506 (189386833 / 100000000000 : ℝ) (378773667 / 200000000000 : ℝ) := by
  exact Encl.add b503 b505 (by norm_num) (by norm_num)

def e507 : ℝ := e8 * e506
lemma b507 : Encl e507 (1855990963 / 1000000000000 : ℝ) (1855990969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b506 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
