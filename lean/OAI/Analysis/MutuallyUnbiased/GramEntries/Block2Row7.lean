import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block64
import OAI.Analysis.MutuallyUnbiased.GramRows.Block72
import OAI.Analysis.MutuallyUnbiased.GramRows.Block73
import OAI.Analysis.MutuallyUnbiased.GramRows.Block74

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_0 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row5160, row5161, row5162, row5163, row5164, row5165, row5166, row5167, row5168, row5169, row5170, row5171, row6178, row6179, row5174, row5175, row6180, row6181, row5176, row5177, row5182, row5183, row6182, row6183, row5184, row5185, row6184, row6185, row6186, row6187, row6188, row6189, row6190, row6191, row6192, row6193, row6194, row6195, row6196, row6197]

theorem entryCheck7_0 : entry7_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_0 k)) := by decide +kernel

theorem rowsSound7_0 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval5160 x
  · exact rowEval5161 x
  · exact rowEval5162 x
  · exact rowEval5163 x
  · exact rowEval5164 x
  · exact rowEval5165 x
  · exact rowEval5166 x
  · exact rowEval5167 x
  · exact rowEval5168 x
  · exact rowEval5169 x
  · exact rowEval5170 x
  · exact rowEval5171 x
  · exact rowEval6178 x
  · exact rowEval6179 x
  · exact rowEval5174 x
  · exact rowEval5175 x
  · exact rowEval6180 x
  · exact rowEval6181 x
  · exact rowEval5176 x
  · exact rowEval5177 x
  · exact rowEval5182 x
  · exact rowEval5183 x
  · exact rowEval6182 x
  · exact rowEval6183 x
  · exact rowEval5184 x
  · exact rowEval5185 x
  · exact rowEval6184 x
  · exact rowEval6185 x
  · exact rowEval6186 x
  · exact rowEval6187 x
  · exact rowEval6188 x
  · exact rowEval6189 x
  · exact rowEval6190 x
  · exact rowEval6191 x
  · exact rowEval6192 x
  · exact rowEval6193 x
  · exact rowEval6194 x
  · exact rowEval6195 x
  · exact rowEval6196 x
  · exact rowEval6197 x

theorem entryEval7_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_0 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck7_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_0]

def rows7_1 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6198, row6199, row6200, row6201, row6202, row6203, row6204, row6205, row6206, row6207, row6208, row6209, row6210, row6211, row6212, row6213, row6214, row6215, row6216, row6217, row6218, row6219, row6220, row6221, row6222, row6223, row6224, row6225, row6226, row6227, row6228, row6229, row6230, row6231, row6232, row6233, row6234, row6235, row6236, row6237]

theorem entryCheck7_1 : entry7_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_1 k)) := by decide +kernel

theorem rowsSound7_1 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval6198 x
  · exact rowEval6199 x
  · exact rowEval6200 x
  · exact rowEval6201 x
  · exact rowEval6202 x
  · exact rowEval6203 x
  · exact rowEval6204 x
  · exact rowEval6205 x
  · exact rowEval6206 x
  · exact rowEval6207 x
  · exact rowEval6208 x
  · exact rowEval6209 x
  · exact rowEval6210 x
  · exact rowEval6211 x
  · exact rowEval6212 x
  · exact rowEval6213 x
  · exact rowEval6214 x
  · exact rowEval6215 x
  · exact rowEval6216 x
  · exact rowEval6217 x
  · exact rowEval6218 x
  · exact rowEval6219 x
  · exact rowEval6220 x
  · exact rowEval6221 x
  · exact rowEval6222 x
  · exact rowEval6223 x
  · exact rowEval6224 x
  · exact rowEval6225 x
  · exact rowEval6226 x
  · exact rowEval6227 x
  · exact rowEval6228 x
  · exact rowEval6229 x
  · exact rowEval6230 x
  · exact rowEval6231 x
  · exact rowEval6232 x
  · exact rowEval6233 x
  · exact rowEval6234 x
  · exact rowEval6235 x
  · exact rowEval6236 x
  · exact rowEval6237 x

theorem entryEval7_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_1 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck7_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_1]

def rows7_2 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6238, row6239, row6240, row6241, row6242, row6243, row6244, row6245, row6246, row6247, row6248, row6249, row6250, row6251, row6252, row6253, row6254, row6255, row6256, row6257, row6258, row6259, row6260, row6261, row6262, row6263, row6264, row6265, row6266, row6267, row6268, row6269, row6270, row6271, row6272, row6273, row6274, row6275, row6276, row6277]

theorem entryCheck7_2 : entry7_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_2 k)) := by decide +kernel

theorem rowsSound7_2 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval6238 x
  · exact rowEval6239 x
  · exact rowEval6240 x
  · exact rowEval6241 x
  · exact rowEval6242 x
  · exact rowEval6243 x
  · exact rowEval6244 x
  · exact rowEval6245 x
  · exact rowEval6246 x
  · exact rowEval6247 x
  · exact rowEval6248 x
  · exact rowEval6249 x
  · exact rowEval6250 x
  · exact rowEval6251 x
  · exact rowEval6252 x
  · exact rowEval6253 x
  · exact rowEval6254 x
  · exact rowEval6255 x
  · exact rowEval6256 x
  · exact rowEval6257 x
  · exact rowEval6258 x
  · exact rowEval6259 x
  · exact rowEval6260 x
  · exact rowEval6261 x
  · exact rowEval6262 x
  · exact rowEval6263 x
  · exact rowEval6264 x
  · exact rowEval6265 x
  · exact rowEval6266 x
  · exact rowEval6267 x
  · exact rowEval6268 x
  · exact rowEval6269 x
  · exact rowEval6270 x
  · exact rowEval6271 x
  · exact rowEval6272 x
  · exact rowEval6273 x
  · exact rowEval6274 x
  · exact rowEval6275 x
  · exact rowEval6276 x
  · exact rowEval6277 x

theorem entryEval7_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_2 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck7_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_2]

def rows7_3 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6278, row6279, row6280, row6281, row6282, row6283, row6284, row6285, row6286, row6287, row6288, row6289, row6290, row6291, row6292, row6293, row6294, row6295, row6296, row6297, row6298, row6299, row6300, row6301, row6302, row6303, row6304, row6305, row6306, row6307, row6308, row6309, row6310, row6311, row6312, row6313, row6314, row6315, row6316, row6317]

theorem entryCheck7_3 : entry7_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_3 k)) := by decide +kernel

theorem rowsSound7_3 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval6278 x
  · exact rowEval6279 x
  · exact rowEval6280 x
  · exact rowEval6281 x
  · exact rowEval6282 x
  · exact rowEval6283 x
  · exact rowEval6284 x
  · exact rowEval6285 x
  · exact rowEval6286 x
  · exact rowEval6287 x
  · exact rowEval6288 x
  · exact rowEval6289 x
  · exact rowEval6290 x
  · exact rowEval6291 x
  · exact rowEval6292 x
  · exact rowEval6293 x
  · exact rowEval6294 x
  · exact rowEval6295 x
  · exact rowEval6296 x
  · exact rowEval6297 x
  · exact rowEval6298 x
  · exact rowEval6299 x
  · exact rowEval6300 x
  · exact rowEval6301 x
  · exact rowEval6302 x
  · exact rowEval6303 x
  · exact rowEval6304 x
  · exact rowEval6305 x
  · exact rowEval6306 x
  · exact rowEval6307 x
  · exact rowEval6308 x
  · exact rowEval6309 x
  · exact rowEval6310 x
  · exact rowEval6311 x
  · exact rowEval6312 x
  · exact rowEval6313 x
  · exact rowEval6314 x
  · exact rowEval6315 x
  · exact rowEval6316 x
  · exact rowEval6317 x

theorem entryEval7_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_3 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck7_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_3]

def rows7_4 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6318, row6319, row6320, row6321, row6322, row6323, row6324, row6325, row6326, row6327, row6328, row6329, row6330, row6331, row6332, row6333, row6334, row6335, row6336, row6337, row6338, row6339, row6340, row6341, row6342, row6343, row6344, row6345, row6346, row6347, row6348, row6349, row6350, row6351, row6352, row6353, row6354, row6355, row6356, row6357]

theorem entryCheck7_4 : entry7_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_4 k)) := by decide +kernel

theorem rowsSound7_4 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval6318 x
  · exact rowEval6319 x
  · exact rowEval6320 x
  · exact rowEval6321 x
  · exact rowEval6322 x
  · exact rowEval6323 x
  · exact rowEval6324 x
  · exact rowEval6325 x
  · exact rowEval6326 x
  · exact rowEval6327 x
  · exact rowEval6328 x
  · exact rowEval6329 x
  · exact rowEval6330 x
  · exact rowEval6331 x
  · exact rowEval6332 x
  · exact rowEval6333 x
  · exact rowEval6334 x
  · exact rowEval6335 x
  · exact rowEval6336 x
  · exact rowEval6337 x
  · exact rowEval6338 x
  · exact rowEval6339 x
  · exact rowEval6340 x
  · exact rowEval6341 x
  · exact rowEval6342 x
  · exact rowEval6343 x
  · exact rowEval6344 x
  · exact rowEval6345 x
  · exact rowEval6346 x
  · exact rowEval6347 x
  · exact rowEval6348 x
  · exact rowEval6349 x
  · exact rowEval6350 x
  · exact rowEval6351 x
  · exact rowEval6352 x
  · exact rowEval6353 x
  · exact rowEval6354 x
  · exact rowEval6355 x
  · exact rowEval6356 x
  · exact rowEval6357 x

theorem entryEval7_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_4 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck7_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_4]

def rows7_5 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6358, row6359, row6360, row6361, row6362, row6363, row6364, row6365, row6366, row6367, row6368, row6369, row6370, row6371, row6372, row6373, row6374, row6375, row6376, row6377, row6378, row6379, row6380, row6381, row6382, row6383, row6384, row6385, row6386, row6387, row6388, row6389, row6390, row6391, row6392, row6393, row6394, row6395, row6396, row6397]

theorem entryCheck7_5 : entry7_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_5 k)) := by decide +kernel

theorem rowsSound7_5 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval6358 x
  · exact rowEval6359 x
  · exact rowEval6360 x
  · exact rowEval6361 x
  · exact rowEval6362 x
  · exact rowEval6363 x
  · exact rowEval6364 x
  · exact rowEval6365 x
  · exact rowEval6366 x
  · exact rowEval6367 x
  · exact rowEval6368 x
  · exact rowEval6369 x
  · exact rowEval6370 x
  · exact rowEval6371 x
  · exact rowEval6372 x
  · exact rowEval6373 x
  · exact rowEval6374 x
  · exact rowEval6375 x
  · exact rowEval6376 x
  · exact rowEval6377 x
  · exact rowEval6378 x
  · exact rowEval6379 x
  · exact rowEval6380 x
  · exact rowEval6381 x
  · exact rowEval6382 x
  · exact rowEval6383 x
  · exact rowEval6384 x
  · exact rowEval6385 x
  · exact rowEval6386 x
  · exact rowEval6387 x
  · exact rowEval6388 x
  · exact rowEval6389 x
  · exact rowEval6390 x
  · exact rowEval6391 x
  · exact rowEval6392 x
  · exact rowEval6393 x
  · exact rowEval6394 x
  · exact rowEval6395 x
  · exact rowEval6396 x
  · exact rowEval6397 x

theorem entryEval7_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_5 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck7_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_5]

def rows7_6 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6398, row6399, row6400, row6401, row6402, row6403, row6404, row6405, row6406, row6407, row6408, row6409, row6410, row6411, row6412, row6413, row6414, row6415, row6416, row6417, row6418, row6419, row6420, row6421, row6422, row6423, row6424, row6425, row6426, row6427, row6428, row6429, row6430, row6431, row6432, row6433, row6434, row6435, row6436, row6437]

theorem entryCheck7_6 : entry7_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_6 k)) := by decide +kernel

theorem rowsSound7_6 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval6398 x
  · exact rowEval6399 x
  · exact rowEval6400 x
  · exact rowEval6401 x
  · exact rowEval6402 x
  · exact rowEval6403 x
  · exact rowEval6404 x
  · exact rowEval6405 x
  · exact rowEval6406 x
  · exact rowEval6407 x
  · exact rowEval6408 x
  · exact rowEval6409 x
  · exact rowEval6410 x
  · exact rowEval6411 x
  · exact rowEval6412 x
  · exact rowEval6413 x
  · exact rowEval6414 x
  · exact rowEval6415 x
  · exact rowEval6416 x
  · exact rowEval6417 x
  · exact rowEval6418 x
  · exact rowEval6419 x
  · exact rowEval6420 x
  · exact rowEval6421 x
  · exact rowEval6422 x
  · exact rowEval6423 x
  · exact rowEval6424 x
  · exact rowEval6425 x
  · exact rowEval6426 x
  · exact rowEval6427 x
  · exact rowEval6428 x
  · exact rowEval6429 x
  · exact rowEval6430 x
  · exact rowEval6431 x
  · exact rowEval6432 x
  · exact rowEval6433 x
  · exact rowEval6434 x
  · exact rowEval6435 x
  · exact rowEval6436 x
  · exact rowEval6437 x

theorem entryEval7_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_6 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck7_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_6]

def rows7_7 : Fin GramFunctions.Block2.form7.size → Integer.Sparse Key := ![row6438, row6439, row6440, row6441, row6442, row6443, row6444, row6445, row6446, row6447, row6448, row6449, row6450, row6451, row6452, row6453, row6454, row6455, row6456, row6457, row6458, row6459, row6460, row6461, row6462, row6463, row6464, row6465, row6466, row6467, row6468, row6469, row6470, row6471, row6472, row6473, row6474, row6475, row6476, row6477]

theorem entryCheck7_7 : entry7_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form7.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form7.terms k).coefficient) (rows7_7 k)) := by decide +kernel

theorem rowsSound7_7 (k : Fin GramFunctions.Block2.form7.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows7_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form7.terms k).tag (GramFunctions.Block2.form7.terms k).charge GramFunctions.Block2.form7) x := by
  fin_cases k
  · exact rowEval6438 x
  · exact rowEval6439 x
  · exact rowEval6440 x
  · exact rowEval6441 x
  · exact rowEval6442 x
  · exact rowEval6443 x
  · exact rowEval6444 x
  · exact rowEval6445 x
  · exact rowEval6446 x
  · exact rowEval6447 x
  · exact rowEval6448 x
  · exact rowEval6449 x
  · exact rowEval6450 x
  · exact rowEval6451 x
  · exact rowEval6452 x
  · exact rowEval6453 x
  · exact rowEval6454 x
  · exact rowEval6455 x
  · exact rowEval6456 x
  · exact rowEval6457 x
  · exact rowEval6458 x
  · exact rowEval6459 x
  · exact rowEval6460 x
  · exact rowEval6461 x
  · exact rowEval6462 x
  · exact rowEval6463 x
  · exact rowEval6464 x
  · exact rowEval6465 x
  · exact rowEval6466 x
  · exact rowEval6467 x
  · exact rowEval6468 x
  · exact rowEval6469 x
  · exact rowEval6470 x
  · exact rowEval6471 x
  · exact rowEval6472 x
  · exact rowEval6473 x
  · exact rowEval6474 x
  · exact rowEval6475 x
  · exact rowEval6476 x
  · exact rowEval6477 x

theorem entryEval7_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry7_7 (GramNormalization.eval B) = GramFunctions.Block2.form7.mixedGram GramFunctions.Block2.form7 B := by
  rw [entryCheck7_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form7 GramFunctions.Block2.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound7_7]

end MUB6.Certificate.GramEntries.Block2

end OAI
