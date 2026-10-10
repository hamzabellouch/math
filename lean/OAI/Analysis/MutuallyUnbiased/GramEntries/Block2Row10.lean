import OAI.Analysis.MutuallyUnbiased.GramEntries.Block2Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramRows.Block78
import OAI.Analysis.MutuallyUnbiased.GramRows.Block79
import OAI.Analysis.MutuallyUnbiased.GramRows.Block80
import OAI.Analysis.MutuallyUnbiased.GramRows.Block81

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7018, row7019, row7020, row7021, row7022, row7023, row7024, row7025, row7026, row7027, row7028, row7029, row7030, row7031, row7032, row7033, row7034, row7035, row7036, row7037, row7038, row7039, row7040, row7041, row7042, row7043, row7044, row7045, row7046, row7047]

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form0) x := by
  fin_cases k
  · exact rowEval7018 x
  · exact rowEval7019 x
  · exact rowEval7020 x
  · exact rowEval7021 x
  · exact rowEval7022 x
  · exact rowEval7023 x
  · exact rowEval7024 x
  · exact rowEval7025 x
  · exact rowEval7026 x
  · exact rowEval7027 x
  · exact rowEval7028 x
  · exact rowEval7029 x
  · exact rowEval7030 x
  · exact rowEval7031 x
  · exact rowEval7032 x
  · exact rowEval7033 x
  · exact rowEval7034 x
  · exact rowEval7035 x
  · exact rowEval7036 x
  · exact rowEval7037 x
  · exact rowEval7038 x
  · exact rowEval7039 x
  · exact rowEval7040 x
  · exact rowEval7041 x
  · exact rowEval7042 x
  · exact rowEval7043 x
  · exact rowEval7044 x
  · exact rowEval7045 x
  · exact rowEval7046 x
  · exact rowEval7047 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

def rows10_1 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7048, row7049, row7050, row7051, row7052, row7053, row7054, row7055, row7056, row7057, row7058, row7059, row7060, row7061, row7062, row7063, row7064, row7065, row7066, row7067, row7068, row7069, row7070, row7071, row7072, row7073, row7074, row7075, row7076, row7077]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval7048 x
  · exact rowEval7049 x
  · exact rowEval7050 x
  · exact rowEval7051 x
  · exact rowEval7052 x
  · exact rowEval7053 x
  · exact rowEval7054 x
  · exact rowEval7055 x
  · exact rowEval7056 x
  · exact rowEval7057 x
  · exact rowEval7058 x
  · exact rowEval7059 x
  · exact rowEval7060 x
  · exact rowEval7061 x
  · exact rowEval7062 x
  · exact rowEval7063 x
  · exact rowEval7064 x
  · exact rowEval7065 x
  · exact rowEval7066 x
  · exact rowEval7067 x
  · exact rowEval7068 x
  · exact rowEval7069 x
  · exact rowEval7070 x
  · exact rowEval7071 x
  · exact rowEval7072 x
  · exact rowEval7073 x
  · exact rowEval7074 x
  · exact rowEval7075 x
  · exact rowEval7076 x
  · exact rowEval7077 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

def rows10_2 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7078, row7079, row7080, row7081, row7082, row7083, row7084, row7085, row7086, row7087, row7088, row7089, row7090, row7091, row7092, row7093, row7094, row7095, row7096, row7097, row7098, row7099, row7100, row7101, row7102, row7103, row7104, row7105, row7106, row7107]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval7078 x
  · exact rowEval7079 x
  · exact rowEval7080 x
  · exact rowEval7081 x
  · exact rowEval7082 x
  · exact rowEval7083 x
  · exact rowEval7084 x
  · exact rowEval7085 x
  · exact rowEval7086 x
  · exact rowEval7087 x
  · exact rowEval7088 x
  · exact rowEval7089 x
  · exact rowEval7090 x
  · exact rowEval7091 x
  · exact rowEval7092 x
  · exact rowEval7093 x
  · exact rowEval7094 x
  · exact rowEval7095 x
  · exact rowEval7096 x
  · exact rowEval7097 x
  · exact rowEval7098 x
  · exact rowEval7099 x
  · exact rowEval7100 x
  · exact rowEval7101 x
  · exact rowEval7102 x
  · exact rowEval7103 x
  · exact rowEval7104 x
  · exact rowEval7105 x
  · exact rowEval7106 x
  · exact rowEval7107 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

def rows10_3 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7108, row7109, row7110, row7111, row7112, row7113, row7114, row7115, row7116, row7117, row7118, row7119, row7120, row7121, row7122, row7123, row7124, row7125, row7126, row7127, row7128, row7129, row7130, row7131, row7132, row7133, row7134, row7135, row7136, row7137]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval7108 x
  · exact rowEval7109 x
  · exact rowEval7110 x
  · exact rowEval7111 x
  · exact rowEval7112 x
  · exact rowEval7113 x
  · exact rowEval7114 x
  · exact rowEval7115 x
  · exact rowEval7116 x
  · exact rowEval7117 x
  · exact rowEval7118 x
  · exact rowEval7119 x
  · exact rowEval7120 x
  · exact rowEval7121 x
  · exact rowEval7122 x
  · exact rowEval7123 x
  · exact rowEval7124 x
  · exact rowEval7125 x
  · exact rowEval7126 x
  · exact rowEval7127 x
  · exact rowEval7128 x
  · exact rowEval7129 x
  · exact rowEval7130 x
  · exact rowEval7131 x
  · exact rowEval7132 x
  · exact rowEval7133 x
  · exact rowEval7134 x
  · exact rowEval7135 x
  · exact rowEval7136 x
  · exact rowEval7137 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

def rows10_4 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7138, row7139, row7140, row7141, row7142, row7143, row7144, row7145, row7146, row7147, row7148, row7149, row7150, row7151, row7152, row7153, row7154, row7155, row7156, row7157, row7158, row7159, row7160, row7161, row7162, row7163, row7164, row7165, row7166, row7167]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval7138 x
  · exact rowEval7139 x
  · exact rowEval7140 x
  · exact rowEval7141 x
  · exact rowEval7142 x
  · exact rowEval7143 x
  · exact rowEval7144 x
  · exact rowEval7145 x
  · exact rowEval7146 x
  · exact rowEval7147 x
  · exact rowEval7148 x
  · exact rowEval7149 x
  · exact rowEval7150 x
  · exact rowEval7151 x
  · exact rowEval7152 x
  · exact rowEval7153 x
  · exact rowEval7154 x
  · exact rowEval7155 x
  · exact rowEval7156 x
  · exact rowEval7157 x
  · exact rowEval7158 x
  · exact rowEval7159 x
  · exact rowEval7160 x
  · exact rowEval7161 x
  · exact rowEval7162 x
  · exact rowEval7163 x
  · exact rowEval7164 x
  · exact rowEval7165 x
  · exact rowEval7166 x
  · exact rowEval7167 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

def rows10_5 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7168, row7169, row7170, row7171, row7172, row7173, row7174, row7175, row7176, row7177, row7178, row7179, row7180, row7181, row7182, row7183, row7184, row7185, row7186, row7187, row7188, row7189, row7190, row7191, row7192, row7193, row7194, row7195, row7196, row7197]

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form5) x := by
  fin_cases k
  · exact rowEval7168 x
  · exact rowEval7169 x
  · exact rowEval7170 x
  · exact rowEval7171 x
  · exact rowEval7172 x
  · exact rowEval7173 x
  · exact rowEval7174 x
  · exact rowEval7175 x
  · exact rowEval7176 x
  · exact rowEval7177 x
  · exact rowEval7178 x
  · exact rowEval7179 x
  · exact rowEval7180 x
  · exact rowEval7181 x
  · exact rowEval7182 x
  · exact rowEval7183 x
  · exact rowEval7184 x
  · exact rowEval7185 x
  · exact rowEval7186 x
  · exact rowEval7187 x
  · exact rowEval7188 x
  · exact rowEval7189 x
  · exact rowEval7190 x
  · exact rowEval7191 x
  · exact rowEval7192 x
  · exact rowEval7193 x
  · exact rowEval7194 x
  · exact rowEval7195 x
  · exact rowEval7196 x
  · exact rowEval7197 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

def rows10_6 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7198, row7199, row7200, row7201, row7202, row7203, row7204, row7205, row7206, row7207, row7208, row7209, row7210, row7211, row7212, row7213, row7214, row7215, row7216, row7217, row7218, row7219, row7220, row7221, row7222, row7223, row7224, row7225, row7226, row7227]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form6) x := by
  fin_cases k
  · exact rowEval7198 x
  · exact rowEval7199 x
  · exact rowEval7200 x
  · exact rowEval7201 x
  · exact rowEval7202 x
  · exact rowEval7203 x
  · exact rowEval7204 x
  · exact rowEval7205 x
  · exact rowEval7206 x
  · exact rowEval7207 x
  · exact rowEval7208 x
  · exact rowEval7209 x
  · exact rowEval7210 x
  · exact rowEval7211 x
  · exact rowEval7212 x
  · exact rowEval7213 x
  · exact rowEval7214 x
  · exact rowEval7215 x
  · exact rowEval7216 x
  · exact rowEval7217 x
  · exact rowEval7218 x
  · exact rowEval7219 x
  · exact rowEval7220 x
  · exact rowEval7221 x
  · exact rowEval7222 x
  · exact rowEval7223 x
  · exact rowEval7224 x
  · exact rowEval7225 x
  · exact rowEval7226 x
  · exact rowEval7227 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

def rows10_7 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7228, row7229, row7230, row7231, row7232, row7233, row7234, row7235, row7236, row7237, row7238, row7239, row7240, row7241, row7242, row7243, row7244, row7245, row7246, row7247, row7248, row7249, row7250, row7251, row7252, row7253, row7254, row7255, row7256, row7257]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form7) x := by
  fin_cases k
  · exact rowEval7228 x
  · exact rowEval7229 x
  · exact rowEval7230 x
  · exact rowEval7231 x
  · exact rowEval7232 x
  · exact rowEval7233 x
  · exact rowEval7234 x
  · exact rowEval7235 x
  · exact rowEval7236 x
  · exact rowEval7237 x
  · exact rowEval7238 x
  · exact rowEval7239 x
  · exact rowEval7240 x
  · exact rowEval7241 x
  · exact rowEval7242 x
  · exact rowEval7243 x
  · exact rowEval7244 x
  · exact rowEval7245 x
  · exact rowEval7246 x
  · exact rowEval7247 x
  · exact rowEval7248 x
  · exact rowEval7249 x
  · exact rowEval7250 x
  · exact rowEval7251 x
  · exact rowEval7252 x
  · exact rowEval7253 x
  · exact rowEval7254 x
  · exact rowEval7255 x
  · exact rowEval7256 x
  · exact rowEval7257 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

def rows10_8 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7258, row7259, row7260, row7261, row7262, row7263, row7264, row7265, row7266, row7267, row7268, row7269, row7270, row7271, row7272, row7273, row7274, row7275, row7276, row7277, row7278, row7279, row7280, row7281, row7282, row7283, row7284, row7285, row7286, row7287]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form8) x := by
  fin_cases k
  · exact rowEval7258 x
  · exact rowEval7259 x
  · exact rowEval7260 x
  · exact rowEval7261 x
  · exact rowEval7262 x
  · exact rowEval7263 x
  · exact rowEval7264 x
  · exact rowEval7265 x
  · exact rowEval7266 x
  · exact rowEval7267 x
  · exact rowEval7268 x
  · exact rowEval7269 x
  · exact rowEval7270 x
  · exact rowEval7271 x
  · exact rowEval7272 x
  · exact rowEval7273 x
  · exact rowEval7274 x
  · exact rowEval7275 x
  · exact rowEval7276 x
  · exact rowEval7277 x
  · exact rowEval7278 x
  · exact rowEval7279 x
  · exact rowEval7280 x
  · exact rowEval7281 x
  · exact rowEval7282 x
  · exact rowEval7283 x
  · exact rowEval7284 x
  · exact rowEval7285 x
  · exact rowEval7286 x
  · exact rowEval7287 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

def rows10_9 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7288, row7289, row7290, row7291, row7292, row7293, row7294, row7295, row7296, row7297, row7298, row7299, row7300, row7301, row7302, row7303, row7304, row7305, row7306, row7307, row7308, row7309, row7310, row7311, row7312, row7313, row7314, row7315, row7316, row7317]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form9) x := by
  fin_cases k
  · exact rowEval7288 x
  · exact rowEval7289 x
  · exact rowEval7290 x
  · exact rowEval7291 x
  · exact rowEval7292 x
  · exact rowEval7293 x
  · exact rowEval7294 x
  · exact rowEval7295 x
  · exact rowEval7296 x
  · exact rowEval7297 x
  · exact rowEval7298 x
  · exact rowEval7299 x
  · exact rowEval7300 x
  · exact rowEval7301 x
  · exact rowEval7302 x
  · exact rowEval7303 x
  · exact rowEval7304 x
  · exact rowEval7305 x
  · exact rowEval7306 x
  · exact rowEval7307 x
  · exact rowEval7308 x
  · exact rowEval7309 x
  · exact rowEval7310 x
  · exact rowEval7311 x
  · exact rowEval7312 x
  · exact rowEval7313 x
  · exact rowEval7314 x
  · exact rowEval7315 x
  · exact rowEval7316 x
  · exact rowEval7317 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

def rows10_10 : Fin GramFunctions.Block2.form10.size → Integer.Sparse Key := ![row7318, row7319, row7320, row7321, row7322, row7323, row7324, row7325, row7326, row7327, row7328, row7329, row7330, row7331, row7332, row7333, row7334, row7335, row7336, row7337, row7338, row7339, row7340, row7341, row7342, row7343, row7344, row7345, row7346, row7347]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form10) x := by
  fin_cases k
  · exact rowEval7318 x
  · exact rowEval7319 x
  · exact rowEval7320 x
  · exact rowEval7321 x
  · exact rowEval7322 x
  · exact rowEval7323 x
  · exact rowEval7324 x
  · exact rowEval7325 x
  · exact rowEval7326 x
  · exact rowEval7327 x
  · exact rowEval7328 x
  · exact rowEval7329 x
  · exact rowEval7330 x
  · exact rowEval7331 x
  · exact rowEval7332 x
  · exact rowEval7333 x
  · exact rowEval7334 x
  · exact rowEval7335 x
  · exact rowEval7336 x
  · exact rowEval7337 x
  · exact rowEval7338 x
  · exact rowEval7339 x
  · exact rowEval7340 x
  · exact rowEval7341 x
  · exact rowEval7342 x
  · exact rowEval7343 x
  · exact rowEval7344 x
  · exact rowEval7345 x
  · exact rowEval7346 x
  · exact rowEval7347 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block2

end OAI
