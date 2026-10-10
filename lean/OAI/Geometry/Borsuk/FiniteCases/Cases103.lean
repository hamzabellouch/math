import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases017
import OAI.Geometry.Borsuk.FiniteCases.Cases018
import OAI.Geometry.Borsuk.FiniteCases.Cases019
import OAI.Geometry.Borsuk.FiniteCases.Cases077

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31532 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 4} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 1, 2, 8} → False := by
  classical
  intro n122 n125 n124 n127 n123 n126
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c4 h u0_121 n122 n123 n124 n125 n126 n127

theorem c31533 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 1, 3, 6} → False := by
  classical
  intro n129 n132 n128 n133 n131 n130
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c19 h u0_121 n128 n129 n130 n131 n132 n133

theorem c31534 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 3, 6} → False := by
  classical
  intro n153 n150 n149 n154 n152 n151
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c124 h u0_121 n149 n150 n151 n152 n153 n154

theorem c31535 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 3, 4} → False := by
  classical
  intro n206 n209 n210 n207 n208 n205
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c544 h u0_121 n205 n206 n207 n208 n209 n210

theorem c31537 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → False := by
  classical
  intro a241 n276 n296 n185
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  exact c1506 h a241 n185 n276 n296 u0_316 u1_317 u2_318

theorem c31538 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → False := by
  classical
  intro a276 n185 n296 n241
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  exact c1508 h a276 n185 n241 n296 u0_316 u1_317 u2_318

theorem c31548 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → False := by
  classical
  intro a278 n243 n187 n298
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u2_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  exact c1538 h a278 n187 n243 n298 u0_317 u1_319 u2_321

theorem c31555 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → False := by
  classical
  intro a189 n300 n280 n245
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1564 h a189 n245 n280 n300 u0_316 u1_322 u2_323

theorem c31556 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro a245 n300 n280 n189
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1566 h a245 n189 n280 n300 u0_316 u1_322 u2_323

theorem c31557 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → False := by
  classical
  intro a280 n245 n189 n300
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1568 h a280 n189 n245 n300 u0_316 u1_322 u2_323

theorem c31558 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → False := by
  classical
  intro a300 n245 n189 n280
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1570 h a300 n189 n245 n280 u0_316 u1_322 u2_323

theorem c31560 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → False := by
  classical
  intro a246 n190 n281 n301
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  exact c1581 h a246 n190 n281 n301 u0_317 u1_322 u2_324

theorem c31563 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → False := by
  classical
  intro a191 n282 n247 n302
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  exact c1594 h a191 n247 n282 n302 u0_318 u1_323 u2_324

theorem c31564 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 9} → Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → False := by
  classical
  intro n302 a247 n282 n191
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  exact c1596 h a247 n191 n282 n302 u0_318 u1_323 u2_324

theorem c31565 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → False := by
  classical
  intro a282 n247 n302 n191
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  exact c1598 h a282 n191 n247 n302 u0_318 u1_323 u2_324

theorem c31572 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → False := by
  classical
  intro n249 n193 a109 n304 n284
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1622 h a109 n193 n249 n284 n304 u0_320 u1_323 u2_325

theorem c31573 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro a193 n284 n249 n304
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1624 h a193 n249 n284 n304 u0_320 u1_323 u2_325

theorem c31574 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro a249 n284 n193 n304
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1626 h a249 n193 n284 n304 u0_320 u1_323 u2_325

theorem c31576 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → Q {3, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → False := by
  classical
  intro n249 n284 a304 n193
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1630 h a304 n193 n249 n284 u0_320 u1_323 u2_325

theorem c31585 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n196 n287 n252 n307 a112
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1667 h a112 n196 n252 n287 n307 u0_317 u1_326 u2_328

theorem c31586 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → False := by
  classical
  intro a196 n287 n252 n307
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1669 h a196 n252 n287 n307 u0_317 u1_326 u2_328

theorem c31587 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a252 n307 n196 n287
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1671 h a252 n196 n287 n307 u0_317 u1_326 u2_328

theorem c31588 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → False := by
  classical
  intro a287 n196 n252 n307
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1673 h a287 n196 n252 n307 u0_317 u1_326 u2_328

theorem c31589 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a307 n252 n196 n287
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1675 h a307 n196 n252 n287 u0_317 u1_326 u2_328

theorem c31594 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → False := by
  classical
  intro a308 n253 n197 n288
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1690 h a308 n197 n253 n288 u0_318 u1_327 u2_328

theorem c31595 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → T {5, 7, 8} → False := by
  classical
  intro n254 n289 n309 n198 a114
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1697 h a114 n198 n254 n289 n309 u0_319 u1_326 u2_329

theorem c31596 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → False := by
  classical
  intro a198 n289 n254 n309
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1699 h a198 n254 n289 n309 u0_319 u1_326 u2_329

theorem c31597 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → False := by
  classical
  intro a254 n309 n289 n198
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1701 h a254 n198 n289 n309 u0_319 u1_326 u2_329

theorem c31598 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → False := by
  classical
  intro a289 n254 n198 n309
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1703 h a289 n198 n254 n309 u0_319 u1_326 u2_329

theorem c31599 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → False := by
  classical
  intro a309 n254 n289 n198
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1705 h a309 n198 n254 n289 u0_319 u1_326 u2_329

end BorsukNine.FiniteObstruction

end OAI
