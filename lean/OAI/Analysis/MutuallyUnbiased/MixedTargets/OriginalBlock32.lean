import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock32 : Integer.Sparse (Fin 2886) := [(1024, -50924900160), (1025, 30220117920), (1026, 1944152640), (1027, -19938131520), (1028, -3106893120), (1029, -18611928000), (1030, -2896158720), (1031, -16533460800), (1032, -73260070080), (1033, 20259264960), (1034, -39648541440), (1035, -12361694400), (1036, 4584015360), (1037, -15823549920), (1038, -30997950720), (1039, 43259212800), (1040, 7492012800), (1041, 46031237280), (1042, -30701108640), (1043, 211086720), (1044, 8197485120), (1045, -19938131520), (1046, -91803287040), (1047, -26223429120), (1048, 18260079360), (1049, -18570432000), (1050, 18614069760), (1051, -18489318240), (1052, 1473098400), (1053, -17255059200), (1054, 14178726720), (1055, -118420945920)]

def originalBlock32 : Integer.Sparse OriginalKey := [(Sum.inl 585, -61808472000), (Sum.inl 590, -14480793600), (Sum.inl 612, -15534465600), (Sum.inl 621, 9720763200), (Sum.inl 909, 230156186400), (Sum.inl 914, 216296064000), (Sum.inl 931, 22920076800), (Sum.inl 940, -82667304000), (Sum.inl 949, -198242707200), (Sum.inl 954, -93059640000), (Sum.inl 1024, -79117749600), (Sum.inl 1047, -366300350400), (Sum.inl 1061, -99690657600), (Sum.inl 1315, 93070348800), (Sum.inl 1323, -131117145600), (Sum.inl 1326, 7365492000), (Sum.inl 1332, -92852160000), (Sum.inl 1336, 91300396800), (Sum.inl 1348, 40987425600), (Sum.inl 1367, 70893633600), (Sum.inl 1369, -99690657600), (Sum.inl 1385, -92446591200), (Sum.inl 1406, -592104729600), (Sum.inl 1408, -459016435200), (Sum.inl 1436, -86275296000), (Sum.inl 1438, 1055433600), (Sum.inl 2323, -153505543200), (Sum.inl 2327, 37460064000), (Sum.inl 2340, -154989753600), (Sum.inl 2346, 101296324800), (Sum.inl 2423, 151100589600), (Sum.inl 3164, -254624500800)]

theorem originalBlockCheck32 : originalBlock32 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock32 keyMomentRows) := by decide +kernel

theorem originalBlockEval32 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock32 x =
      Integer.Sparse.eval keyPolynomialBlock32 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck32, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
