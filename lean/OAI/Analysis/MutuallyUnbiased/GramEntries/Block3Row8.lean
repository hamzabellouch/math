import OAI.Analysis.MutuallyUnbiased.GramEntries.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramRows.Block86
import OAI.Analysis.MutuallyUnbiased.GramRows.Block87
import OAI.Analysis.MutuallyUnbiased.GramRows.Block88

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows8_0 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7945, row7946, row7947, row7948, row7949, row7950, row7951, row7952, row7953, row7954, row7955, row7956, row7957, row7958, row7959, row7960, row7961, row7962, row7963, row7964, row7965, row7966, row7967, row7968, row7969, row7970, row7971, row7972, row7973, row7974, row7975, row7976, row7977, row7978, row7979, row7980]

theorem entryCheck8_0 : entry8_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_0 k)) := by decide +kernel

theorem rowsSound8_0 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval7945 x
  · exact rowEval7946 x
  · exact rowEval7947 x
  · exact rowEval7948 x
  · exact rowEval7949 x
  · exact rowEval7950 x
  · exact rowEval7951 x
  · exact rowEval7952 x
  · exact rowEval7953 x
  · exact rowEval7954 x
  · exact rowEval7955 x
  · exact rowEval7956 x
  · exact rowEval7957 x
  · exact rowEval7958 x
  · exact rowEval7959 x
  · exact rowEval7960 x
  · exact rowEval7961 x
  · exact rowEval7962 x
  · exact rowEval7963 x
  · exact rowEval7964 x
  · exact rowEval7965 x
  · exact rowEval7966 x
  · exact rowEval7967 x
  · exact rowEval7968 x
  · exact rowEval7969 x
  · exact rowEval7970 x
  · exact rowEval7971 x
  · exact rowEval7972 x
  · exact rowEval7973 x
  · exact rowEval7974 x
  · exact rowEval7975 x
  · exact rowEval7976 x
  · exact rowEval7977 x
  · exact rowEval7978 x
  · exact rowEval7979 x
  · exact rowEval7980 x

theorem entryEval8_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_0 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck8_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_0]

def rows8_1 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row7981, row7982, row7983, row7984, row7985, row7986, row7987, row7988, row7989, row7990, row7991, row7992, row7993, row7994, row7995, row7996, row7997, row7998, row7999, row8000, row8001, row8002, row8003, row8004, row8005, row8006, row8007, row8008, row8009, row8010, row8011, row8012, row8013, row8014, row8015, row8016]

theorem entryCheck8_1 : entry8_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_1 k)) := by decide +kernel

theorem rowsSound8_1 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval7981 x
  · exact rowEval7982 x
  · exact rowEval7983 x
  · exact rowEval7984 x
  · exact rowEval7985 x
  · exact rowEval7986 x
  · exact rowEval7987 x
  · exact rowEval7988 x
  · exact rowEval7989 x
  · exact rowEval7990 x
  · exact rowEval7991 x
  · exact rowEval7992 x
  · exact rowEval7993 x
  · exact rowEval7994 x
  · exact rowEval7995 x
  · exact rowEval7996 x
  · exact rowEval7997 x
  · exact rowEval7998 x
  · exact rowEval7999 x
  · exact rowEval8000 x
  · exact rowEval8001 x
  · exact rowEval8002 x
  · exact rowEval8003 x
  · exact rowEval8004 x
  · exact rowEval8005 x
  · exact rowEval8006 x
  · exact rowEval8007 x
  · exact rowEval8008 x
  · exact rowEval8009 x
  · exact rowEval8010 x
  · exact rowEval8011 x
  · exact rowEval8012 x
  · exact rowEval8013 x
  · exact rowEval8014 x
  · exact rowEval8015 x
  · exact rowEval8016 x

theorem entryEval8_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_1 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck8_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_1]

def rows8_2 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8017, row8018, row8019, row8020, row8021, row8022, row8023, row8024, row8025, row8026, row8027, row8028, row8029, row8030, row8031, row8032, row8033, row8034, row8035, row8036, row8037, row8038, row8039, row8040, row8041, row8042, row8043, row8044, row8045, row8046, row8047, row8048, row8049, row8050, row8051, row8052]

theorem entryCheck8_2 : entry8_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_2 k)) := by decide +kernel

theorem rowsSound8_2 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval8017 x
  · exact rowEval8018 x
  · exact rowEval8019 x
  · exact rowEval8020 x
  · exact rowEval8021 x
  · exact rowEval8022 x
  · exact rowEval8023 x
  · exact rowEval8024 x
  · exact rowEval8025 x
  · exact rowEval8026 x
  · exact rowEval8027 x
  · exact rowEval8028 x
  · exact rowEval8029 x
  · exact rowEval8030 x
  · exact rowEval8031 x
  · exact rowEval8032 x
  · exact rowEval8033 x
  · exact rowEval8034 x
  · exact rowEval8035 x
  · exact rowEval8036 x
  · exact rowEval8037 x
  · exact rowEval8038 x
  · exact rowEval8039 x
  · exact rowEval8040 x
  · exact rowEval8041 x
  · exact rowEval8042 x
  · exact rowEval8043 x
  · exact rowEval8044 x
  · exact rowEval8045 x
  · exact rowEval8046 x
  · exact rowEval8047 x
  · exact rowEval8048 x
  · exact rowEval8049 x
  · exact rowEval8050 x
  · exact rowEval8051 x
  · exact rowEval8052 x

theorem entryEval8_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_2 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck8_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_2]

def rows8_3 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8053, row8054, row8055, row8056, row8057, row8058, row8059, row8060, row8061, row8062, row8063, row8064, row8065, row8066, row8067, row8068, row8069, row8070, row8071, row8072, row8073, row8074, row8075, row8076, row8077, row8078, row8079, row8080, row8081, row8082, row8083, row8084, row8085, row8086, row8087, row8088]

theorem entryCheck8_3 : entry8_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_3 k)) := by decide +kernel

theorem rowsSound8_3 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval8053 x
  · exact rowEval8054 x
  · exact rowEval8055 x
  · exact rowEval8056 x
  · exact rowEval8057 x
  · exact rowEval8058 x
  · exact rowEval8059 x
  · exact rowEval8060 x
  · exact rowEval8061 x
  · exact rowEval8062 x
  · exact rowEval8063 x
  · exact rowEval8064 x
  · exact rowEval8065 x
  · exact rowEval8066 x
  · exact rowEval8067 x
  · exact rowEval8068 x
  · exact rowEval8069 x
  · exact rowEval8070 x
  · exact rowEval8071 x
  · exact rowEval8072 x
  · exact rowEval8073 x
  · exact rowEval8074 x
  · exact rowEval8075 x
  · exact rowEval8076 x
  · exact rowEval8077 x
  · exact rowEval8078 x
  · exact rowEval8079 x
  · exact rowEval8080 x
  · exact rowEval8081 x
  · exact rowEval8082 x
  · exact rowEval8083 x
  · exact rowEval8084 x
  · exact rowEval8085 x
  · exact rowEval8086 x
  · exact rowEval8087 x
  · exact rowEval8088 x

theorem entryEval8_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_3 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck8_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_3]

def rows8_4 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8089, row8090, row8091, row8092, row8093, row8094, row8095, row8096, row8097, row8098, row8099, row8100, row8101, row8102, row8103, row8104, row8105, row8106, row8107, row8108, row8109, row8110, row8111, row8112, row8113, row8114, row8115, row8116, row8117, row8118, row8119, row8120, row8121, row8122, row8123, row8124]

theorem entryCheck8_4 : entry8_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_4 k)) := by decide +kernel

theorem rowsSound8_4 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval8089 x
  · exact rowEval8090 x
  · exact rowEval8091 x
  · exact rowEval8092 x
  · exact rowEval8093 x
  · exact rowEval8094 x
  · exact rowEval8095 x
  · exact rowEval8096 x
  · exact rowEval8097 x
  · exact rowEval8098 x
  · exact rowEval8099 x
  · exact rowEval8100 x
  · exact rowEval8101 x
  · exact rowEval8102 x
  · exact rowEval8103 x
  · exact rowEval8104 x
  · exact rowEval8105 x
  · exact rowEval8106 x
  · exact rowEval8107 x
  · exact rowEval8108 x
  · exact rowEval8109 x
  · exact rowEval8110 x
  · exact rowEval8111 x
  · exact rowEval8112 x
  · exact rowEval8113 x
  · exact rowEval8114 x
  · exact rowEval8115 x
  · exact rowEval8116 x
  · exact rowEval8117 x
  · exact rowEval8118 x
  · exact rowEval8119 x
  · exact rowEval8120 x
  · exact rowEval8121 x
  · exact rowEval8122 x
  · exact rowEval8123 x
  · exact rowEval8124 x

theorem entryEval8_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_4 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck8_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_4]

def rows8_5 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8125, row8126, row8127, row8128, row8129, row8130, row8131, row8132, row8133, row8134, row8135, row8136, row8137, row8138, row8139, row8140, row8141, row8142, row8143, row8144, row8145, row8146, row8147, row8148, row8149, row8150, row8151, row8152, row8153, row8154, row8155, row8156, row8157, row8158, row8159, row8160]

theorem entryCheck8_5 : entry8_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_5 k)) := by decide +kernel

theorem rowsSound8_5 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval8125 x
  · exact rowEval8126 x
  · exact rowEval8127 x
  · exact rowEval8128 x
  · exact rowEval8129 x
  · exact rowEval8130 x
  · exact rowEval8131 x
  · exact rowEval8132 x
  · exact rowEval8133 x
  · exact rowEval8134 x
  · exact rowEval8135 x
  · exact rowEval8136 x
  · exact rowEval8137 x
  · exact rowEval8138 x
  · exact rowEval8139 x
  · exact rowEval8140 x
  · exact rowEval8141 x
  · exact rowEval8142 x
  · exact rowEval8143 x
  · exact rowEval8144 x
  · exact rowEval8145 x
  · exact rowEval8146 x
  · exact rowEval8147 x
  · exact rowEval8148 x
  · exact rowEval8149 x
  · exact rowEval8150 x
  · exact rowEval8151 x
  · exact rowEval8152 x
  · exact rowEval8153 x
  · exact rowEval8154 x
  · exact rowEval8155 x
  · exact rowEval8156 x
  · exact rowEval8157 x
  · exact rowEval8158 x
  · exact rowEval8159 x
  · exact rowEval8160 x

theorem entryEval8_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_5 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck8_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_5]

def rows8_6 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8161, row8162, row8163, row8164, row8165, row8166, row8167, row8168, row8169, row8170, row8171, row8172, row8173, row8174, row8175, row8176, row8177, row8178, row8179, row8180, row8181, row8182, row8183, row8184, row8185, row8186, row8187, row8188, row8189, row8190, row8191, row8192, row8193, row8194, row8195, row8196]

theorem entryCheck8_6 : entry8_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_6 k)) := by decide +kernel

theorem rowsSound8_6 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval8161 x
  · exact rowEval8162 x
  · exact rowEval8163 x
  · exact rowEval8164 x
  · exact rowEval8165 x
  · exact rowEval8166 x
  · exact rowEval8167 x
  · exact rowEval8168 x
  · exact rowEval8169 x
  · exact rowEval8170 x
  · exact rowEval8171 x
  · exact rowEval8172 x
  · exact rowEval8173 x
  · exact rowEval8174 x
  · exact rowEval8175 x
  · exact rowEval8176 x
  · exact rowEval8177 x
  · exact rowEval8178 x
  · exact rowEval8179 x
  · exact rowEval8180 x
  · exact rowEval8181 x
  · exact rowEval8182 x
  · exact rowEval8183 x
  · exact rowEval8184 x
  · exact rowEval8185 x
  · exact rowEval8186 x
  · exact rowEval8187 x
  · exact rowEval8188 x
  · exact rowEval8189 x
  · exact rowEval8190 x
  · exact rowEval8191 x
  · exact rowEval8192 x
  · exact rowEval8193 x
  · exact rowEval8194 x
  · exact rowEval8195 x
  · exact rowEval8196 x

theorem entryEval8_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_6 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck8_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_6]

def rows8_7 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8197, row8198, row8199, row8200, row8201, row8202, row8203, row8204, row8205, row8206, row8207, row8208, row8209, row8210, row8211, row8212, row8213, row8214, row8215, row8216, row8217, row8218, row8219, row8220, row8221, row8222, row8223, row8224, row8225, row8226, row8227, row8228, row8229, row8230, row8231, row8232]

theorem entryCheck8_7 : entry8_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_7 k)) := by decide +kernel

theorem rowsSound8_7 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval8197 x
  · exact rowEval8198 x
  · exact rowEval8199 x
  · exact rowEval8200 x
  · exact rowEval8201 x
  · exact rowEval8202 x
  · exact rowEval8203 x
  · exact rowEval8204 x
  · exact rowEval8205 x
  · exact rowEval8206 x
  · exact rowEval8207 x
  · exact rowEval8208 x
  · exact rowEval8209 x
  · exact rowEval8210 x
  · exact rowEval8211 x
  · exact rowEval8212 x
  · exact rowEval8213 x
  · exact rowEval8214 x
  · exact rowEval8215 x
  · exact rowEval8216 x
  · exact rowEval8217 x
  · exact rowEval8218 x
  · exact rowEval8219 x
  · exact rowEval8220 x
  · exact rowEval8221 x
  · exact rowEval8222 x
  · exact rowEval8223 x
  · exact rowEval8224 x
  · exact rowEval8225 x
  · exact rowEval8226 x
  · exact rowEval8227 x
  · exact rowEval8228 x
  · exact rowEval8229 x
  · exact rowEval8230 x
  · exact rowEval8231 x
  · exact rowEval8232 x

theorem entryEval8_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_7 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck8_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_7]

def rows8_8 : Fin GramFunctions.Block3.form8.size → Integer.Sparse Key := ![row8233, row8234, row8235, row8236, row8237, row8238, row8239, row8240, row8241, row8242, row8243, row8244, row8245, row8246, row8247, row8248, row8249, row8250, row8251, row8252, row8253, row8254, row8255, row8256, row8257, row8258, row8259, row8260, row8261, row8262, row8263, row8264, row8265, row8266, row8267, row8268]

theorem entryCheck8_8 : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

theorem rowsSound8_8 (k : Fin GramFunctions.Block3.form8.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows8_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form8.terms k).tag (GramFunctions.Block3.form8.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval8233 x
  · exact rowEval8234 x
  · exact rowEval8235 x
  · exact rowEval8236 x
  · exact rowEval8237 x
  · exact rowEval8238 x
  · exact rowEval8239 x
  · exact rowEval8240 x
  · exact rowEval8241 x
  · exact rowEval8242 x
  · exact rowEval8243 x
  · exact rowEval8244 x
  · exact rowEval8245 x
  · exact rowEval8246 x
  · exact rowEval8247 x
  · exact rowEval8248 x
  · exact rowEval8249 x
  · exact rowEval8250 x
  · exact rowEval8251 x
  · exact rowEval8252 x
  · exact rowEval8253 x
  · exact rowEval8254 x
  · exact rowEval8255 x
  · exact rowEval8256 x
  · exact rowEval8257 x
  · exact rowEval8258 x
  · exact rowEval8259 x
  · exact rowEval8260 x
  · exact rowEval8261 x
  · exact rowEval8262 x
  · exact rowEval8263 x
  · exact rowEval8264 x
  · exact rowEval8265 x
  · exact rowEval8266 x
  · exact rowEval8267 x
  · exact rowEval8268 x

theorem entryEval8_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry8_8 (GramNormalization.eval B) = GramFunctions.Block3.form8.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck8_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form8 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound8_8]

end MUB6.Certificate.GramEntries.Block3

end OAI
