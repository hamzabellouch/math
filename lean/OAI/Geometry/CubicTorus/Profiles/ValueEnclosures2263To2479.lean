import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures2042To2262

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
lemma b2262 : Encl e2262 (-184054689471 / 500000000000 : ℝ) (-368109378927 / 1000000000000 : ℝ) := by
  exact Encl.add b2245 b2261 (by norm_num) (by norm_num)

def e2263 : ℝ := e2233 ^ 2
lemma b2263 : Encl e2263 (834417854083 / 1000000000000 : ℝ) (104302231761 / 125000000000 : ℝ) := by
  exact Encl.pow b2233 (by norm_num) 2 (by norm_num) (by norm_num)

def e2264 : ℝ := e5 - e2263
lemma b2264 : Encl e2264 (20697768239 / 125000000000 : ℝ) (165582145917 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2263 (by norm_num) (by norm_num)

def e2265 : ℝ := Real.sqrt e2264
lemma b2265 : Encl e2265 (203458930691 / 500000000000 : ℝ) (406917861389 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2264 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2266 : ℝ := e5 + e2265
lemma b2266 : Encl e2266 (703458930691 / 500000000000 : ℝ) (1406917861389 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2265 (by norm_num) (by norm_num)

def e2267 : ℝ := e2233 / e2266
lemma b2267 : Encl e2267 (324633291531 / 500000000000 : ℝ) (649266583067 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2266 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2268 : ℝ := e2267 ^ 2
lemma b2268 : Encl e2268 (421547095881 / 1000000000000 : ℝ) (26346693493 / 62500000000 : ℝ) := by
  exact Encl.pow b2267 (by norm_num) 2 (by norm_num) (by norm_num)

def e2269 : ℝ := e5 + e2268
lemma b2269 : Encl e2269 (1421547095881 / 1000000000000 : ℝ) (88846693493 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2268 (by norm_num) (by norm_num)

def e2270 : ℝ := Real.sqrt e2269
lemma b2270 : Encl e2270 (298071624769 / 250000000000 : ℝ) (29807162477 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2269 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2271 : ℝ := e5 + e2270
lemma b2271 : Encl e2271 (548071624769 / 250000000000 : ℝ) (54807162477 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2270 (by norm_num) (by norm_num)

def e2272 : ℝ := e2267 / e2271
lemma b2272 : Encl e2272 (29615955001 / 100000000000 : ℝ) (148079775007 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2267 b2271 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2273 : ℝ := Real.arcsin e2233
lemma b2273 : Encl e2273 (1151718929409 / 1000000000000 : ℝ) (575859464713 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e2233) (a := (29615955001 / 100000000000 : ℝ)) (b := (148079775007 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (913464752513 / 1000000000000 : ℝ) by norm_num).trans b2233.1
        exact b2233.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2233) (29615955001 / 100000000000 : ℝ) (148079775007 / 500000000000 : ℝ) from b2272) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2274 : ℝ := e59 * e2273
lemma b2274 : Encl e2274 (293688326999 / 500000000000 : ℝ) (73422081751 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2273 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2275 : ℝ := e61 * e2233
lemma b2275 : Encl e2275 (447597728731 / 1000000000000 : ℝ) (447597728733 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2233 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2276 : ℝ := e2275 * e2265
lemma b2276 : Encl e2276 (91067755267 / 500000000000 : ℝ) (182135510539 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2275 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2277 : ℝ := e2274 - e2276
lemma b2277 : Encl e2277 (405241143459 / 1000000000000 : ℝ) (202620571737 / 500000000000 : ℝ) := by
  exact Encl.sub b2274 b2276 (by norm_num) (by norm_num)

def e2278 : ℝ := e43 * e2265
lemma b2278 : Encl e2278 (203458930691 / 10000000000 : ℝ) (406917861389 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2279 : ℝ := e2233 / e2278
lemma b2279 : Encl e2279 (5612095457 / 125000000000 : ℝ) (22448381829 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2278 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2280 : ℝ := e2277 - e2279
lemma b2280 : Encl e2280 (360344379801 / 1000000000000 : ℝ) (180172189909 / 500000000000 : ℝ) := by
  exact Encl.sub b2277 b2279 (by norm_num) (by norm_num)

def e2281 : ℝ := e5 + e2249
lemma b2281 : Encl e2281 (238058867593 / 125000000000 : ℝ) (952235470373 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2249 (by norm_num) (by norm_num)

def e2282 : ℝ := e2232 / e2281
lemma b2282 : Encl e2282 (44793043397 / 200000000000 : ℝ) (111982608493 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2232 b2281 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2283 : ℝ := e2282 ^ 2
lemma b2283 : Encl e2283 (50160418419 / 1000000000000 : ℝ) (2508020921 / 50000000000 : ℝ) := by
  exact Encl.pow b2282 (by norm_num) 2 (by norm_num) (by norm_num)

def e2284 : ℝ := e5 + e2283
lemma b2284 : Encl e2284 (1050160418419 / 1000000000000 : ℝ) (52508020921 / 50000000000 : ℝ) := by
  exact Encl.add b5 b2283 (by norm_num) (by norm_num)

def e2285 : ℝ := Real.sqrt e2284
lemma b2285 : Encl e2285 (1024773349779 / 1000000000000 : ℝ) (1024773349781 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2284 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2286 : ℝ := e5 + e2285
lemma b2286 : Encl e2286 (2024773349779 / 1000000000000 : ℝ) (2024773349781 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2285 (by norm_num) (by norm_num)

def e2287 : ℝ := e2282 / e2286
lemma b2287 : Encl e2287 (11061248757 / 100000000000 : ℝ) (110612487571 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2282 b2286 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2288 : ℝ := Real.arcsin e2232
lemma b2288 : Encl e2288 (220329302981 / 500000000000 : ℝ) (440658605967 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2232) (a := (11061248757 / 100000000000 : ℝ)) (b := (110612487571 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (213267623743 / 500000000000 : ℝ) by norm_num).trans b2232.1
        exact b2232.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2232) (11061248757 / 100000000000 : ℝ) (110612487571 / 1000000000000 : ℝ) from b2287) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2289 : ℝ := e59 * e2288
lemma b2289 : Encl e2289 (2809198613 / 12500000000 : ℝ) (56183972261 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2288 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2290 : ℝ := e61 * e2232
lemma b2290 : Encl e2290 (52250567817 / 250000000000 : ℝ) (209002271269 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2232 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2291 : ℝ := e2290 * e2249
lemma b2291 : Encl e2291 (189036480911 / 1000000000000 : ℝ) (189036480913 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2290 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2292 : ℝ := e2289 - e2291
lemma b2292 : Encl e2292 (35699408127 / 1000000000000 : ℝ) (35699408133 / 1000000000000 : ℝ) := by
  exact Encl.sub b2289 b2291 (by norm_num) (by norm_num)

def e2293 : ℝ := e43 * e2249
lemma b2293 : Encl e2293 (113058867593 / 2500000000 : ℝ) (452235470373 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2249 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2294 : ℝ := e2232 / e2293
lemma b2294 : Encl e2294 (9431707051 / 1000000000000 : ℝ) (2357926763 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2232 b2293 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2295 : ℝ := e2292 - e2294
lemma b2295 : Encl e2295 (1050708043 / 40000000000 : ℝ) (13133850541 / 500000000000 : ℝ) := by
  exact Encl.sub b2292 b2294 (by norm_num) (by norm_num)

def e2296 : ℝ := e2280 - e2295
lemma b2296 : Encl e2296 (334076678719 / 1000000000000 : ℝ) (334076678743 / 1000000000000 : ℝ) := by
  exact Encl.sub b2280 b2295 (by norm_num) (by norm_num)

def e2297 : ℝ := e2296 / e2231
lemma b2297 : Encl e2297 (249310954267 / 1000000000000 : ℝ) (124655477143 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2296 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2298 : ℝ := e2262 + e2297
lemma b2298 : Encl e2298 (-4751936987 / 40000000000 : ℝ) (-118798424641 / 1000000000000 : ℝ) := by
  exact Encl.add b2262 b2297 (by norm_num) (by norm_num)

def e2299 : ℝ := e2233 + e4
lemma b2299 : Encl e2299 (1903208071123 / 1000000000000 : ℝ) (951604035563 / 500000000000 : ℝ) := by
  exact Encl.add b2233 b4 (by norm_num) (by norm_num)

def e2300 : ℝ := e2299 / e23
lemma b2300 : Encl e2300 (951604035561 / 1000000000000 : ℝ) (951604035563 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2299 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2301 : ℝ := e2233 / e2231
lemma b2301 : Encl e2301 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2233 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2302 : ℝ := e89 * e2301
lemma b2302 : Encl e2302 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2301 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2303 : ℝ := e2301 ^ 2
lemma b2303 : Encl e2303 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2301 (by norm_num) 2 (by norm_num) (by norm_num)

def e2304 : ℝ := e91 * e2303
lemma b2304 : Encl e2304 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2305 : ℝ := e5 + e2304
lemma b2305 : Encl e2305 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2304 (by norm_num) (by norm_num)

def e2306 : ℝ := Real.sqrt e2305
lemma b2306 : Encl e2306 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2305 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2307 : ℝ := e2302 * e2306
lemma b2307 : Encl e2307 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2302 b2306 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2308 : ℝ := e97 * e2303
lemma b2308 : Encl e2308 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2303 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2309 : ℝ := e2307 - e2308
lemma b2309 : Encl e2309 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2307 b2308 (by norm_num) (by norm_num)

def e2310 : ℝ := e2300 * e2309
lemma b2310 : Encl e2310 (324349531649 / 500000000000 : ℝ) (648699063323 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2300 b2309 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2311 : ℝ := e2300 / e2231
lemma b2311 : Encl e2311 (5548064573 / 7812500000 : ℝ) (355076132673 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2312 : ℝ := e89 * e2311
lemma b2312 : Encl e2312 (1258712117437 / 1000000000000 : ℝ) (1258712117443 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2311 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2313 : ℝ := e2311 ^ 2
lemma b2313 : Encl e2313 (504316239973 / 1000000000000 : ℝ) (504316239977 / 1000000000000 : ℝ) := by
  exact Encl.pow b2311 (by norm_num) 2 (by norm_num) (by norm_num)

def e2314 : ℝ := e91 * e2313
lemma b2314 : Encl e2314 (198044524323 / 500000000000 : ℝ) (7921780973 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2315 : ℝ := e5 + e2314
lemma b2315 : Encl e2315 (698044524323 / 500000000000 : ℝ) (27921780973 / 20000000000 : ℝ) := by
  exact Encl.add b5 b2314 (by norm_num) (by norm_num)

def e2316 : ℝ := Real.sqrt e2315
lemma b2316 : Encl e2316 (1181562122211 / 1000000000000 : ℝ) (590781061107 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2315 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2317 : ℝ := e2312 * e2316
lemma b2317 : Encl e2317 (1487246560731 / 1000000000000 : ℝ) (1487246560743 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2312 b2316 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2318 : ℝ := e97 * e2313
lemma b2318 : Encl e2318 (198044524323 / 250000000000 : ℝ) (792178097299 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2313 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2319 : ℝ := e2317 - e2318
lemma b2319 : Encl e2319 (86883557929 / 125000000000 : ℝ) (695068463451 / 1000000000000 : ℝ) := by
  exact Encl.sub b2317 b2318 (by norm_num) (by norm_num)

def e2320 : ℝ := e2233 * e2319
lemma b2320 : Encl e2320 (79365067741 / 125000000000 : ℝ) (158730135487 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2233 b2319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2321 : ℝ := e2310 - e2320
lemma b2321 : Encl e2321 (275570427 / 20000000000 : ℝ) (2755704279 / 200000000000 : ℝ) := by
  exact Encl.sub b2310 b2320 (by norm_num) (by norm_num)

def e2322 : ℝ := e2300 ^ 2
lemma b2322 : Encl e2322 (181110048099 / 200000000000 : ℝ) (1811100481 / 2000000000 : ℝ) := by
  exact Encl.pow b2300 (by norm_num) 2 (by norm_num) (by norm_num)

def e2323 : ℝ := e8 * e2322
lemma b2323 : Encl e2323 (177487847137 / 200000000000 : ℝ) (88743923569 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2322 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2324 : ℝ := e5 - e2323
lemma b2324 : Encl e2324 (11256076431 / 100000000000 : ℝ) (22512152863 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2323 (by norm_num) (by norm_num)

def e2325 : ℝ := e5 - e2322
lemma b2325 : Encl e2325 (188899519 / 2000000000 : ℝ) (18889951901 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2322 (by norm_num) (by norm_num)

def e2326 : ℝ := Real.sqrt e2325
lemma b2326 : Encl e2326 (61465359187 / 200000000000 : ℝ) (38415849493 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2325 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2327 : ℝ := e2324 / e2326
lemma b2327 : Encl e2327 (183128783099 / 500000000000 : ℝ) (183128783113 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2324 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2328 : ℝ := e5 - e2327
lemma b2328 : Encl e2328 (316871216887 / 500000000000 : ℝ) (316871216901 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2327 (by norm_num) (by norm_num)

def e2329 : ℝ := e8 * e2263
lemma b2329 : Encl e2329 (817729497001 / 1000000000000 : ℝ) (817729497007 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2263 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2330 : ℝ := e5 - e2329
lemma b2330 : Encl e2330 (182270502993 / 1000000000000 : ℝ) (182270502999 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2329 (by norm_num) (by norm_num)

def e2331 : ℝ := e2330 / e2265
lemma b2331 : Encl e2331 (17917178899 / 40000000000 : ℝ) (447929472499 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2330 b2265 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2332 : ℝ := e5 - e2331
lemma b2332 : Encl e2332 (552070527501 / 1000000000000 : ℝ) (22082821101 / 40000000000 : ℝ) := by
  exact Encl.sub b5 b2331 (by norm_num) (by norm_num)

def e2333 : ℝ := e2328 - e2332
lemma b2333 : Encl e2333 (81671906249 / 1000000000000 : ℝ) (81671906301 / 1000000000000 : ℝ) := by
  exact Encl.sub b2328 b2332 (by norm_num) (by norm_num)

def e2334 : ℝ := e2321 * e2333
lemma b2334 : Encl e2334 (1125318103 / 1000000000000 : ℝ) (1125318109 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2321 b2333 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2335 : ℝ := e2319 - e2309
lemma b2335 : Encl e2335 (3344587401 / 250000000000 : ℝ) (6689174823 / 500000000000 : ℝ) := by
  exact Encl.sub b2319 b2309 (by norm_num) (by norm_num)

def e2336 : ℝ := e5 + e2326
lemma b2336 : Encl e2336 (261465359187 / 200000000000 : ℝ) (163415849493 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2326 (by norm_num) (by norm_num)

def e2337 : ℝ := e2300 / e2336
lemma b2337 : Encl e2337 (727900658437 / 1000000000000 : ℝ) (145580131689 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2336 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2338 : ℝ := e2337 ^ 2
lemma b2338 : Encl e2338 (529839368553 / 1000000000000 : ℝ) (105967873713 / 200000000000 : ℝ) := by
  exact Encl.pow b2337 (by norm_num) 2 (by norm_num) (by norm_num)

def e2339 : ℝ := e5 + e2338
lemma b2339 : Encl e2339 (1529839368553 / 1000000000000 : ℝ) (305967873713 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2338 (by norm_num) (by norm_num)

def e2340 : ℝ := Real.sqrt e2339
lemma b2340 : Encl e2340 (618433377283 / 500000000000 : ℝ) (309216688643 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2339 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2341 : ℝ := e5 + e2340
lemma b2341 : Encl e2341 (1118433377283 / 500000000000 : ℝ) (559216688643 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2340 (by norm_num) (by norm_num)

def e2342 : ℝ := e2337 / e2341
lemma b2342 : Encl e2342 (2033817663 / 6250000000 : ℝ) (65082165217 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2337 b2341 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2343 : ℝ := Real.arcsin e2300
lemma b2343 : Encl e2343 (251682745869 / 200000000000 : ℝ) (2013461967 / 1600000000 : ℝ) := by
  apply Encl.arcsin (z := e2300) (a := (2033817663 / 6250000000 : ℝ)) (b := (65082165217 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (951604035561 / 1000000000000 : ℝ) by norm_num).trans b2300.1
        exact b2300.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2300) (2033817663 / 6250000000 : ℝ) (65082165217 / 200000000000 : ℝ) from b2342) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2344 : ℝ := e59 * e2343
lemma b2344 : Encl e2344 (128358200393 / 200000000000 : ℝ) (320895500991 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2343 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2345 : ℝ := e61 * e2300
lemma b2345 : Encl e2345 (29142873589 / 62500000000 : ℝ) (233142988713 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2300 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2346 : ℝ := e2345 * e2326
lemma b2346 : Encl e2346 (143302175431 / 1000000000000 : ℝ) (35825543859 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2345 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2347 : ℝ := e2344 - e2346
lemma b2347 : Encl e2347 (498488826529 / 1000000000000 : ℝ) (498488826551 / 1000000000000 : ℝ) := by
  exact Encl.sub b2344 b2346 (by norm_num) (by norm_num)

def e2348 : ℝ := e43 * e2326
lemma b2348 : Encl e2348 (61465359187 / 4000000000 : ℝ) (38415849493 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2326 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2349 : ℝ := e2300 / e2348
lemma b2349 : Encl e2349 (61927827193 / 1000000000000 : ℝ) (15481956799 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2300 b2348 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2350 : ℝ := e2347 - e2349
lemma b2350 : Encl e2350 (436560999333 / 1000000000000 : ℝ) (218280499679 / 500000000000 : ℝ) := by
  exact Encl.sub b2347 b2349 (by norm_num) (by norm_num)

def e2351 : ℝ := e2350 - e2280
lemma b2351 : Encl e2351 (15243323903 / 200000000000 : ℝ) (76216619557 / 1000000000000 : ℝ) := by
  exact Encl.sub b2350 b2280 (by norm_num) (by norm_num)

def e2352 : ℝ := e2335 * e2351
lemma b2352 : Encl e2352 (1019652581 / 1000000000000 : ℝ) (509826293 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2335 b2351 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2353 : ℝ := e2334 + e2352
lemma b2353 : Encl e2353 (536242671 / 250000000000 : ℝ) (428994139 / 200000000000 : ℝ) := by
  exact Encl.add b2334 b2352 (by norm_num) (by norm_num)

def e2354 : ℝ := e2300 - e2233
lemma b2354 : Encl e2354 (19069641523 / 500000000000 : ℝ) (762785661 / 20000000000 : ℝ) := by
  exact Encl.sub b2300 b2233 (by norm_num) (by norm_num)

def e2355 : ℝ := e2353 / e2354
lemma b2355 : Encl e2355 (1406011409 / 25000000000 : ℝ) (11248091331 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2353 b2354 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2356 : ℝ := e2298 + e2355
lemma b2356 : Encl e2356 (-12511593663 / 200000000000 : ℝ) (-31278983993 / 500000000000 : ℝ) := by
  exact Encl.add b2298 b2355 (by norm_num) (by norm_num)

def e2357 : ℝ := e4 * e2319
lemma b2357 : Encl e2357 (343969683829 / 500000000000 : ℝ) (343969683839 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2319 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2358 : ℝ := e4 / e2231
lemma b2358 : Encl e2358 (738614416873 / 1000000000000 : ℝ) (369307208437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2359 : ℝ := e89 * e2358
lemma b2359 : Encl e2359 (8182249797 / 6250000000 : ℝ) (327289991881 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2358 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2360 : ℝ := e2358 ^ 2
lemma b2360 : Encl e2360 (136387814203 / 250000000000 : ℝ) (109110251363 / 200000000000 : ℝ) := by
  exact Encl.pow b2358 (by norm_num) 2 (by norm_num) (by norm_num)

def e2361 : ℝ := e91 * e2360
lemma b2361 : Encl e2361 (428474955139 / 1000000000000 : ℝ) (214237477571 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2362 : ℝ := e5 + e2361
lemma b2362 : Encl e2362 (1428474955139 / 1000000000000 : ℝ) (714237477571 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2361 (by norm_num) (by norm_num)

def e2363 : ℝ := Real.sqrt e2362
lemma b2363 : Encl e2363 (29879706273 / 25000000000 : ℝ) (1195188250923 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2362 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2364 : ℝ := e2359 * e2363
lemma b2364 : Encl e2364 (782346305877 / 500000000000 : ℝ) (391173152941 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2359 b2363 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2365 : ℝ := e97 * e2360
lemma b2365 : Encl e2365 (428474955139 / 500000000000 : ℝ) (214237477571 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2366 : ℝ := e2364 - e2365
lemma b2366 : Encl e2366 (70774270147 / 100000000000 : ℝ) (353871350743 / 500000000000 : ℝ) := by
  exact Encl.sub b2364 b2365 (by norm_num) (by norm_num)

def e2367 : ℝ := e2300 * e2366
lemma b2367 : Encl e2367 (673490810857 / 1000000000000 : ℝ) (5387926487 / 8000000000 : ℝ) := by
  exact Encl.mul_nonneg b2300 b2366 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2368 : ℝ := e2357 - e2367
lemma b2368 : Encl e2368 (14448556783 / 1000000000000 : ℝ) (14448556821 / 1000000000000 : ℝ) := by
  exact Encl.sub b2357 b2367 (by norm_num) (by norm_num)

def e2369 : ℝ := e165 - e2328
lemma b2369 : Encl e2369 (86257566173 / 1000000000000 : ℝ) (43128783127 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2328 (by norm_num) (by norm_num)

def e2370 : ℝ := e2368 * e2369
lemma b2370 : Encl e2370 (623148671 / 500000000000 : ℝ) (311574337 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2368 b2369 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2371 : ℝ := e2366 - e2319
lemma b2371 : Encl e2371 (12674238019 / 1000000000000 : ℝ) (6337119027 / 500000000000 : ℝ) := by
  exact Encl.sub b2366 b2319 (by norm_num) (by norm_num)

def e2372 : ℝ := e183 - e2350
lemma b2372 : Encl e2372 (41795885077 / 500000000000 : ℝ) (8359177031 / 100000000000 : ℝ) := by
  exact Encl.sub b183 b2350 (by norm_num) (by norm_num)

def e2373 : ℝ := e2371 * e2372
lemma b2373 : Encl e2373 (1059461991 / 1000000000000 : ℝ) (1059461997 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2371 b2372 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2374 : ℝ := e2370 + e2373
lemma b2374 : Encl e2374 (2305759333 / 1000000000000 : ℝ) (461151869 / 200000000000 : ℝ) := by
  exact Encl.add b2370 b2373 (by norm_num) (by norm_num)

def e2375 : ℝ := e4 - e2300
lemma b2375 : Encl e2375 (38139283047 / 1000000000000 : ℝ) (762785661 / 20000000000 : ℝ) := by
  exact Encl.sub b4 b2300 (by norm_num) (by norm_num)

def e2376 : ℝ := e2374 / e2375
lemma b2376 : Encl e2376 (3022814207 / 50000000000 : ℝ) (60456284461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2374 b2375 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2377 : ℝ := e2356 + e2376
lemma b2377 : Encl e2377 (-84067367 / 40000000000 : ℝ) (-84067341 / 40000000000 : ℝ) := by
  exact Encl.add b2356 b2376 (by norm_num) (by norm_num)

def e2378 : ℝ := e924 / e2231
lemma b2378 : Encl e2378 (716417910447 / 1000000000000 : ℝ) (44776119403 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2379 : ℝ := min e7 e2378
lemma b2379 : Encl e2379 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2378 (by norm_num) (by norm_num)

def e2380 : ℝ := e2379 - e5
lemma b2380 : Encl e2380 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2379 b5 (by norm_num) (by norm_num)

def e2381 : ℝ := e23 * e2231
lemma b2381 : Encl e2381 (67 / 25 : ℝ) (67 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2231 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2382 : ℝ := e2381 * e2242
lemma b2382 : Encl e2382 (76223092127 / 40000000000 : ℝ) (1905577303179 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2381 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2383 : ℝ := e2382 / e0
lemma b2383 : Encl e2383 (75820511811 / 125000000000 : ℝ) (60656409449 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2382 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2384 : ℝ := e2380 + e2383
lemma b2384 : Encl e2384 (18015888019 / 62500000000 : ℝ) (288254208307 / 1000000000000 : ℝ) := by
  exact Encl.add b2380 b2383 (by norm_num) (by norm_num)

def e2385 : ℝ := e23 * e2236
lemma b2385 : Encl e2385 (4489 / 1250 : ℝ) (4489 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2236 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2386 : ℝ := e2385 * e2242
lemma b2386 : Encl e2386 (510694717251 / 200000000000 : ℝ) (2553473586259 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2385 b2242 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2387 : ℝ := e0 + e2386
lemma b2387 : Encl e2387 (1423766559961 / 250000000000 : ℝ) (5695066239849 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2386 (by norm_num) (by norm_num)

def e2388 : ℝ := Real.sqrt e2387
lemma b2388 : Encl e2388 (2386433791213 / 1000000000000 : ℝ) (477286758243 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2387 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2389 : ℝ := e932 * e2388
lemma b2389 : Encl e2389 (151925093693 / 100000000000 : ℝ) (303850187387 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2388 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2390 : ℝ := e2231 ^ 3
lemma b2390 : Encl e2390 (300763 / 125000 : ℝ) (300763 / 125000 : ℝ) := by
  exact Encl.pow b2231 (by norm_num) 3 (by norm_num) (by norm_num)

def e2391 : ℝ := e939 * e2390
lemma b2391 : Encl e2391 (20151121 / 62500000 : ℝ) (20151121 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2390 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2392 : ℝ := min e2391 e941
lemma b2392 : Encl e2392 (20151121 / 62500000 : ℝ) (20151121 / 62500000 : ℝ) := by
  exact Encl.min b2391 b941 (by norm_num) (by norm_num)

def e2393 : ℝ := e23 * e2384
lemma b2393 : Encl e2393 (18015888019 / 31250000000 : ℝ) (288254208307 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2394 : ℝ := e944 * e2392
lemma b2394 : Encl e2394 (60453363 / 31250000 : ℝ) (60453363 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2392 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2395 : ℝ := e2389 ^ 2
lemma b2395 : Encl e2395 (1154061704681 / 500000000000 : ℝ) (1154061704689 / 500000000000 : ℝ) := by
  exact Encl.pow b2389 (by norm_num) 2 (by norm_num) (by norm_num)

def e2396 : ℝ := e2394 * e2395
lemma b2396 : Encl e2396 (2232541157039 / 500000000000 : ℝ) (446508231411 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b2394 b2395 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2397 : ℝ := e2396 * e2384
lemma b2397 : Encl e2397 (40221211483 / 31250000000 : ℝ) (32176969187 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b2396 b2384 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2398 : ℝ := e2397 / e9
lemma b2398 : Encl e2398 (4596709883771 / 1000000000000 : ℝ) (2298354941929 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2397 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2399 : ℝ := e5 + e2398
lemma b2399 : Encl e2399 (5596709883771 / 1000000000000 : ℝ) (2798354941929 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2398 (by norm_num) (by norm_num)

def e2400 : ℝ := Real.sqrt e2399
lemma b2400 : Encl e2400 (2365736647171 / 1000000000000 : ℝ) (2365736647191 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2399 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2401 : ℝ := e5 + e2400
lemma b2401 : Encl e2401 (3365736647171 / 1000000000000 : ℝ) (3365736647191 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2400 (by norm_num) (by norm_num)

def e2402 : ℝ := e2393 / e2401
lemma b2402 : Encl e2402 (171287440771 / 1000000000000 : ℝ) (6851497631 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2393 b2401 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2403 : ℝ := e2392 * e954
lemma b2403 : Encl e2403 (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2392 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2404 : ℝ := e2384 - e2402
lemma b2404 : Encl e2404 (116966767529 / 1000000000000 : ℝ) (7310422971 / 62500000000 : ℝ) := by
  exact Encl.sub b2384 b2402 (by norm_num) (by norm_num)

def e2405 : ℝ := e2404 / e2389
lemma b2405 : Encl e2405 (15397952331 / 200000000000 : ℝ) (76989761661 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2404 b2389 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2406 : ℝ := e2405 ^ 2
lemma b2406 : Encl e2406 (5927423399 / 1000000000000 : ℝ) (5927423401 / 1000000000000 : ℝ) := by
  exact Encl.pow b2405 (by norm_num) 2 (by norm_num) (by norm_num)

def e2407 : ℝ := e9 * e2406
lemma b2407 : Encl e2407 (1659678551 / 1000000000000 : ℝ) (1659678553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2406 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2408 : ℝ := e2402 ^ 3
lemma b2408 : Encl e2408 (201018743 / 40000000000 : ℝ) (5025468577 / 1000000000000 : ℝ) := by
  exact Encl.pow b2402 (by norm_num) 3 (by norm_num) (by norm_num)

def e2409 : ℝ := e2392 * e2408
lemma b2409 : Encl e2409 (324060241 / 200000000000 : ℝ) (1620301207 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2392 b2408 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2410 : ℝ := e2407 + e2409
lemma b2410 : Encl e2410 (819994939 / 250000000000 : ℝ) (40999747 / 12500000000 : ℝ) := by
  exact Encl.add b2407 b2409 (by norm_num) (by norm_num)

def e2411 : ℝ := min e2403 e2410
lemma b2411 : Encl e2411 (597182501 / 200000000000 : ℝ) (1492956253 / 500000000000 : ℝ) := by
  exact Encl.min b2403 b2410 (by norm_num) (by norm_num)

def e2412 : ℝ := (69 / 50 : ℝ)
lemma b2412 : Encl e2412 (69 / 50 : ℝ) (69 / 50 : ℝ) := by
  exact Encl.exact (69 / 50 : ℝ)

def e2413 : ℝ := e2412 / e0
lemma b2413 : Encl e2413 (439267642933 / 1000000000000 : ℝ) (219633821467 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2412 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2414 : ℝ := e2412 * e7
lemma b2414 : Encl e2414 (470366178533 / 500000000000 : ℝ) (235183089267 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2412 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2415 : ℝ := e8 * e2412
lemma b2415 : Encl e2415 (3381 / 2500 : ℝ) (3381 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2416 : ℝ := e2415 / e0
lemma b2416 : Encl e2416 (215241145037 / 500000000000 : ℝ) (17219291603 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2415 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2417 : ℝ := e2412 ^ 2
lemma b2417 : Encl e2417 (4761 / 2500 : ℝ) (4761 / 2500 : ℝ) := by
  exact Encl.pow b2412 (by norm_num) 2 (by norm_num) (by norm_num)

def e2418 : ℝ := e17 * e2417
lemma b2418 : Encl e2418 (4761 / 625 : ℝ) (4761 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2419 : ℝ := e2418 / e0
lemma b2419 : Encl e2419 (2424757388993 / 1000000000000 : ℝ) (1212378694497 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2418 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2420 : ℝ := e5 + e2419
lemma b2420 : Encl e2420 (3424757388993 / 1000000000000 : ℝ) (1712378694497 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2419 (by norm_num) (by norm_num)

def e2421 : ℝ := Real.sqrt e2420
lemma b2421 : Encl e2421 (462652501141 / 250000000000 : ℝ) (370122000913 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2420 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2422 : ℝ := e5 + e2421
lemma b2422 : Encl e2422 (712652501141 / 250000000000 : ℝ) (570122000913 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2421 (by norm_num) (by norm_num)

def e2423 : ℝ := e23 / e2422
lemma b2423 : Encl e2423 (701604216921 / 1000000000000 : ℝ) (350802108461 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2422 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2424 : ℝ := e9 * e2423
lemma b2424 : Encl e2424 (196449180737 / 1000000000000 : ℝ) (196449180739 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2425 : ℝ := e2416 + e2424
lemma b2425 : Encl e2425 (626931470811 / 1000000000000 : ℝ) (313465735407 / 500000000000 : ℝ) := by
  exact Encl.add b2416 b2424 (by norm_num) (by norm_num)

def e2426 : ℝ := e2425 - e5
lemma b2426 : Encl e2426 (-373068529189 / 1000000000000 : ℝ) (-186534264593 / 500000000000 : ℝ) := by
  exact Encl.sub b2425 b5 (by norm_num) (by norm_num)

def e2427 : ℝ := e0 / e2417
lemma b2427 : Encl e2427 (824824788277 / 500000000000 : ℝ) (329929915311 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2428 : ℝ := e2413 ^ 2
lemma b2428 : Encl e2428 (192956062127 / 1000000000000 : ℝ) (192956062129 / 1000000000000 : ℝ) := by
  exact Encl.pow b2413 (by norm_num) 2 (by norm_num) (by norm_num)

def e2429 : ℝ := e5 - e2428
lemma b2429 : Encl e2429 (807043937871 / 1000000000000 : ℝ) (807043937873 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2428 (by norm_num) (by norm_num)

def e2430 : ℝ := Real.sqrt e2429
lemma b2430 : Encl e2430 (112294530273 / 125000000000 : ℝ) (449178121093 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2429 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2431 : ℝ := e29 - e2430
lemma b2431 : Encl e2431 (-1448059847 / 6250000000 : ℝ) (-231689575517 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2430 (by norm_num) (by norm_num)

def e2432 : ℝ := e2430 ^ 3
lemma b2432 : Encl e2432 (725012959303 / 1000000000000 : ℝ) (181253239827 / 250000000000 : ℝ) := by
  exact Encl.pow b2430 (by norm_num) 3 (by norm_num) (by norm_num)

def e2433 : ℝ := e2432 / e35
lemma b2433 : Encl e2433 (120835493217 / 500000000000 : ℝ) (60417746609 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2432 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2434 : ℝ := e2431 + e2433
lemma b2434 : Encl e2434 (4990705457 / 500000000000 : ℝ) (9981410919 / 1000000000000 : ℝ) := by
  exact Encl.add b2431 b2433 (by norm_num) (by norm_num)

def e2435 : ℝ := e8 * e2434
lemma b2435 : Encl e2435 (1956356539 / 200000000000 : ℝ) (9781782701 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2434 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2436 : ℝ := e2428 / e2430
lemma b2436 : Encl e2436 (214787912707 / 1000000000000 : ℝ) (214787912711 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2428 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2437 : ℝ := e2436 - e23
lemma b2437 : Encl e2437 (-1785212087293 / 1000000000000 : ℝ) (-1785212087289 / 1000000000000 : ℝ) := by
  exact Encl.sub b2436 b23 (by norm_num) (by norm_num)

def e2438 : ℝ := e23 * e2430
lemma b2438 : Encl e2438 (112294530273 / 62500000000 : ℝ) (449178121093 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2439 : ℝ := e2437 + e2438
lemma b2439 : Encl e2439 (460015883 / 40000000000 : ℝ) (11500397083 / 1000000000000 : ℝ) := by
  exact Encl.add b2437 b2438 (by norm_num) (by norm_num)

def e2440 : ℝ := e2439 / e43
lemma b2440 : Encl e2440 (230007941 / 1000000000000 : ℝ) (115003971 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2439 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2441 : ℝ := e2435 - e2440
lemma b2441 : Encl e2441 (9551774753 / 1000000000000 : ℝ) (238794369 / 25000000000 : ℝ) := by
  exact Encl.sub b2435 b2440 (by norm_num) (by norm_num)

def e2442 : ℝ := e2427 * e2441
lemma b2442 : Encl e2442 (1969635147 / 125000000000 : ℝ) (15757081189 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2427 b2441 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2443 : ℝ := e2426 + e2442
lemma b2443 : Encl e2443 (-357311448013 / 1000000000000 : ℝ) (-357311447997 / 1000000000000 : ℝ) := by
  exact Encl.add b2426 b2442 (by norm_num) (by norm_num)

def e2444 : ℝ := e2414 ^ 2
lemma b2444 : Encl e2444 (88497736763 / 100000000000 : ℝ) (176995473527 / 200000000000 : ℝ) := by
  exact Encl.pow b2414 (by norm_num) 2 (by norm_num) (by norm_num)

def e2445 : ℝ := e5 - e2444
lemma b2445 : Encl e2445 (23004526473 / 200000000000 : ℝ) (11502263237 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b2444 (by norm_num) (by norm_num)

def e2446 : ℝ := Real.sqrt e2445
lemma b2446 : Encl e2446 (84787466779 / 250000000000 : ℝ) (84787466781 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2445 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2447 : ℝ := e5 + e2446
lemma b2447 : Encl e2447 (334787466779 / 250000000000 : ℝ) (334787466781 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2446 (by norm_num) (by norm_num)

def e2448 : ℝ := e2414 / e2447
lemma b2448 : Encl e2448 (702484748093 / 1000000000000 : ℝ) (7024847481 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2449 : ℝ := e2448 ^ 2
lemma b2449 : Encl e2449 (493484821303 / 1000000000000 : ℝ) (246742410657 / 500000000000 : ℝ) := by
  exact Encl.pow b2448 (by norm_num) 2 (by norm_num) (by norm_num)

def e2450 : ℝ := e5 + e2449
lemma b2450 : Encl e2450 (1493484821303 / 1000000000000 : ℝ) (746742410657 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2449 (by norm_num) (by norm_num)

def e2451 : ℝ := Real.sqrt e2450
lemma b2451 : Encl e2451 (611041083173 / 500000000000 : ℝ) (76380135397 / 62500000000 : ℝ) := by
  exact Encl.sqrt b2450 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2452 : ℝ := e5 + e2451
lemma b2452 : Encl e2452 (1111041083173 / 500000000000 : ℝ) (138880135397 / 62500000000 : ℝ) := by
  exact Encl.add b5 b2451 (by norm_num) (by norm_num)

def e2453 : ℝ := e2448 / e2452
lemma b2453 : Encl e2453 (316138061287 / 1000000000000 : ℝ) (79034515323 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2448 b2452 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2454 : ℝ := Real.arcsin e2414
lemma b2454 : Encl e2454 (1224783269243 / 1000000000000 : ℝ) (1224783269269 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2414) (a := (316138061287 / 1000000000000 : ℝ)) (b := (79034515323 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (470366178533 / 500000000000 : ℝ) by norm_num).trans b2414.1
        exact b2414.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2414) (316138061287 / 1000000000000 : ℝ) (79034515323 / 250000000000 : ℝ) from b2453) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2455 : ℝ := e59 * e2454
lemma b2455 : Encl e2455 (624639467313 / 1000000000000 : ℝ) (9759991677 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2454 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2456 : ℝ := e61 * e2414
lemma b2456 : Encl e2456 (230479427481 / 500000000000 : ℝ) (115239713741 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2414 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2457 : ℝ := e2456 * e2446
lemma b2457 : Encl e2457 (78167067203 / 500000000000 : ℝ) (156334134411 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2456 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2458 : ℝ := e2455 - e2457
lemma b2458 : Encl e2458 (234152666451 / 500000000000 : ℝ) (234152666461 / 500000000000 : ℝ) := by
  exact Encl.sub b2455 b2457 (by norm_num) (by norm_num)

def e2459 : ℝ := e43 * e2446
lemma b2459 : Encl e2459 (84787466779 / 5000000000 : ℝ) (84787466781 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2460 : ℝ := e2414 / e2459
lemma b2460 : Encl e2460 (55475908927 / 1000000000000 : ℝ) (55475908929 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2459 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2461 : ℝ := e2458 - e2460
lemma b2461 : Encl e2461 (412829423973 / 1000000000000 : ℝ) (82565884799 / 200000000000 : ℝ) := by
  exact Encl.sub b2458 b2460 (by norm_num) (by norm_num)

def e2462 : ℝ := e5 + e2430
lemma b2462 : Encl e2462 (237294530273 / 125000000000 : ℝ) (949178121093 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2430 (by norm_num) (by norm_num)

def e2463 : ℝ := e2413 / e2462
lemma b2463 : Encl e2463 (115696841607 / 500000000000 : ℝ) (14462105201 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2413 b2462 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2464 : ℝ := e2463 ^ 2
lemma b2464 : Encl e2464 (53543036631 / 1000000000000 : ℝ) (53543036633 / 1000000000000 : ℝ) := by
  exact Encl.pow b2463 (by norm_num) 2 (by norm_num) (by norm_num)

def e2465 : ℝ := e5 + e2464
lemma b2465 : Encl e2465 (1053543036631 / 1000000000000 : ℝ) (1053543036633 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2464 (by norm_num) (by norm_num)

def e2466 : ℝ := Real.sqrt e2465
lemma b2466 : Encl e2466 (513211222751 / 500000000000 : ℝ) (16037850711 / 15625000000 : ℝ) := by
  exact Encl.sqrt b2465 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2467 : ℝ := e5 + e2466
lemma b2467 : Encl e2467 (1013211222751 / 500000000000 : ℝ) (31662850711 / 15625000000 : ℝ) := by
  exact Encl.add b5 b2466 (by norm_num) (by norm_num)

def e2468 : ℝ := e2463 / e2467
lemma b2468 : Encl e2468 (114188274871 / 1000000000000 : ℝ) (57094137437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2463 b2467 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2469 : ℝ := Real.arcsin e2413
lemma b2469 : Encl e2469 (227391645883 / 500000000000 : ℝ) (454783291779 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e2413) (a := (114188274871 / 1000000000000 : ℝ)) (b := (57094137437 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (439267642933 / 1000000000000 : ℝ) by norm_num).trans b2413.1
        exact b2413.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2413) (114188274871 / 1000000000000 : ℝ) (57094137437 / 500000000000 : ℝ) from b2468) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2470 : ℝ := e59 * e2469
lemma b2470 : Encl e2470 (579848697 / 2500000000 : ℝ) (28992434851 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2469 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2471 : ℝ := e61 * e2413
lemma b2471 : Encl e2471 (215241145037 / 1000000000000 : ℝ) (107620572519 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2413 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2472 : ℝ := e2471 * e2430
lemma b2472 : Encl e2472 (96681613109 / 500000000000 : ℝ) (193363226221 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2471 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2473 : ℝ := e2470 - e2472
lemma b2473 : Encl e2473 (38576252579 / 1000000000000 : ℝ) (3857625259 / 100000000000 : ℝ) := by
  exact Encl.sub b2470 b2472 (by norm_num) (by norm_num)

def e2474 : ℝ := e43 * e2430
lemma b2474 : Encl e2474 (112294530273 / 2500000000 : ℝ) (449178121093 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2430 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2475 : ℝ := e2413 / e2474
lemma b2475 : Encl e2475 (9779364183 / 1000000000000 : ℝ) (1222420523 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b2413 b2474 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2476 : ℝ := e2473 - e2475
lemma b2476 : Encl e2476 (5759377679 / 200000000000 : ℝ) (28796888407 / 1000000000000 : ℝ) := by
  exact Encl.sub b2473 b2475 (by norm_num) (by norm_num)

def e2477 : ℝ := e2461 - e2476
lemma b2477 : Encl e2477 (192016267783 / 500000000000 : ℝ) (960081339 / 2500000000 : ℝ) := by
  exact Encl.sub b2461 b2476 (by norm_num) (by norm_num)

def e2478 : ℝ := e2477 / e2412
lemma b2478 : Encl e2478 (139142223031 / 500000000000 : ℝ) (278284446087 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2477 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2479 : ℝ := e2443 + e2478
lemma b2479 : Encl e2479 (-79027001951 / 1000000000000 : ℝ) (-7902700191 / 100000000000 : ℝ) := by
  exact Encl.add b2443 b2478 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
